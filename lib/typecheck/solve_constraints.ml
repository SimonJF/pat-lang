(* Pattern constraint solution. Follows a similar approach to the CobaltBlue
   paper and MCC.

   Alas, MCC and CobaltBlue have different definitions of upper and lower bounds
   (in MCC, a lower bound is a constraint where the pattern variable is on the
   RHS, and an upper bound is a constraint where the RHS is a guarded pattern).

   Invariant is that the system should consist only of a set of lower bounds and
   a set of upper bounds (i.e., RHS of each constraint must either be a single
   pattern variable, or contain no pattern variables).

   Here, we describe the MCC solution as this is closest to what we do.

   1. Calculate lower bounds for constraints (that is, constraints whose LHS is
       a pattern variable). If a pattern variable is contained within the
       constraint set but is not an lower bound, instantiate it with 0 (the
       largest pattern).

   2. Group the lower bounds, so there is one constraint per type variable.

   3. Compute the Hopkins-Kozen solution of each lower bound equation.

   4. Substitute each type variable through the remainder of the system of
       equations.

   5. Check whether the system of equations is satisfiable.
       - Translate into a semilinear set
       - Translate semilinear set into a Presburger formula
       - Translate Presburger formula into internal solver representation, ship
           to solver

   6. If satisfiable, then substitute the solutions for each type variable in
       the program, and return the program without type variables.
*)
open Common
open Util.Utility
open Type

module PVarMap = StringMap

(* Recall: Lower bound is a constraint where pattern variable is on the RHS *)
(* Want to generate a mapping between pattern variables and the patterns that feed into them. *)
let get_lower_bounds =
    List.filter_map (fun x ->
        match Constraint.rhs x with
            | PatVar p -> Some (p, Constraint.lhs x)
            | _ -> None)

(* Recall: Upper bound is a constraint where RHS is defined *)
let get_upper_bounds =
    List.filter (fun x -> Pattern.defined (Constraint.rhs x))

(* Given the set of pattern variables in the constraint set,
   and a list of lower bounds, return a mapping from each pattern variable to
   a pattern. Duplicates are handled by adding a pattern disjunction; unbounded
   variables are set to the largest pattern (Zero). *)
let group_lower_bounds
    (pat_vars : StringSet.t)
    (lower_bounds : (PatternVar.t * Pattern.t) list)
    : Pattern.t PVarMap.t =
    let open Pattern in

    (* Group all patterns *)
    Settings.if_debug (fun () -> Printf.printf "Lower bounds:\n");
    let grouped =
        List.fold_left (fun acc (pv, pat) ->
            Settings.if_debug (fun () ->
                Format.(fprintf std_formatter "%s |-> %a\n" pv Pattern.pp pat)
            );
            match PVarMap.find_opt pv acc with
                | Some pat2 ->
                    PVarMap.add pv (Plus (pat, pat2)) acc
                | None ->
                    PVarMap.add pv pat acc
        ) PVarMap.empty lower_bounds
    in
    (* Then, compute set of variables which aren't lower bounds,
       and initialise them to Zero. We should then have a mapping
       for each pattern variable contained in the constraint set.
     *)
    let bounds_set =
        PVarMap.bindings grouped
            |> List.map fst
            |> StringSet.of_list in
    let unbounded_vars =
        StringSet.diff pat_vars bounds_set
            |> StringSet.elements
    in
    List.fold_left
        (fun acc x -> PVarMap.add x Zero acc)
        grouped unbounded_vars

(* Follow the same logic as MCC.
   Iterate from top-to-bottom, building up a substitution map with the resolved
   pattern, and resolving each pattern in turn.
   Then, iterate from bottom to top.
   Finally, simplify the system.
 *)
let substitute_solutions constrs =
    let cmp (x1, _) (y1, _) = compare x1 y1 in
    (* Top-to-bottom *)
    let top_to_bottom =
        List.fold_left (fun (map: Pattern.t stringmap) (var, pat) ->
            let hk_sol =
                (* Apply current substitution map to pattern *)
                Pattern.subst_all pat map
                (* Compute HK solution *)
                |> Pattern.hopkins_kozen_solution var
                (* Simplify*)
                |> Pattern.simplify
            in
            Settings.if_debug (fun () ->
                Format.printf "HK Solution for %s: %a\n" var Pattern.pp hk_sol
            );
            PVarMap.add var hk_sol map
        ) PVarMap.empty (PVarMap.bindings constrs |> List.stable_sort (cmp))
    in
    (* Bottom to top *)
    let bottom_to_top =
        List.fold_left (fun map (var, pat) ->
            let pat = Pattern.subst_all pat map in
            PVarMap.add var pat map
        )
         PVarMap.empty
        (PVarMap.bindings top_to_bottom |> List.stable_sort (cmp) |> List.rev)
    in
    (* Simplify constraint system *)
    PVarMap.mapi (
        fun key pat ->
            let simp = Pattern.simplify pat in
            Settings.if_debug (fun () ->
                Format.(fprintf
                    std_formatter "SIMPLIFYING %s(%a): %a\n"
                        key Pattern.pp pat Pattern.pp simp)
            );
            simp) bottom_to_top

(* Satisfiability checking. *)
open Semilinear


(* The base of a linear set is translated to a conjunction of constraints
   demanding that each tag appears the specified number of times.
   For example, < 2 x Get, 1 x Put > is translated as (Get = 2 && Put = 1).
 *)
let base_tuple base =
    let open Presburger in
    TagBag.fold
        (fun tag count acc -> conj (tag_eq_lit tag count) acc)
        base
        Presburger.tt

(* Given a set of tags in the system, converts a linear set into a Presburger
   formula. *)
let linear_to_presburger tags (base, periods) =
    let open Presburger in
    (* Far easier to treat periods as a list *)
    let periods = PeriodSet.elements periods in
    (* Each period requires a fresh variable, which will be existentially
       quantified. *)
    let period_vars =
        List.init (List.length periods) (Printf.sprintf "$v%d")
    in
    (* Need to explicitly encode that each coefficient must be non-negative *)
    let nonneg v = Rel (LE, Int 0, Var v) in
    (* Wrap the expression in existential binders for all period variables. *)
    let bind_existentials e =
        let nonnegs =
            List.fold_right (fun x acc -> conj (nonneg x) acc) period_vars e
        in
        List.fold_right (fun x acc -> Exists (x, acc)) period_vars nonnegs
    in
    (* Compute clause for a particular tag *)
    let tag_clause tag =
        (* tag =
            <base value of tag> +
            <period variable 1 * period 1 value of tag> +
            ... +
            <period variable n * period n value of tag>
        *)
        let base_val = Int (TagBag.occ tag base) in
        let periods_with_vars = List.combine period_vars periods in
        let period_val =
            List.fold_right
                (fun (var, period) acc ->
                    let p_mul = Mul (TagBag.occ tag period, Var var) in
                    plus p_mul acc)
                periods_with_vars
                (Int 0)
        in
        tag_eq tag (plus base_val period_val)
    in
    List.fold_right
        (fun tag -> conj (tag_clause tag))
            tags Presburger.True
        |> bind_existentials


let semilinear_to_presburger tags sls =
    SemiLinearSet.elements sls (* Linear set list*)
    |> List.map (linear_to_presburger tags) (* Presburger list *)
    |> (flip (List.fold_right (Presburger.disj))) Presburger.False (* Presburger *)


let resolve_constraint resolved_lowers constr =
    let lhs, rhs = Constraint.(lhs constr, rhs constr) in
    (* Pattern should be an upper bound, and therefore have no variables on its
     RHS. *)
    let () = assert (Pattern.defined rhs) in
    (* Substitute in solutions for all pattern variables, and simplify *)
    let lhs =
        Pattern.subst_all lhs resolved_lowers
            |> Pattern.simplify
    in
    let rhs = Pattern.simplify rhs in
    Constraint.make lhs rhs

(* Translates a constraint into the inclusion between semilinear sets that we
   need to decide. *)
(* PRECONDITION: Requires the constraint to be fully resolved *)
let constraint_to_semilinear constr =
    let lhs, rhs = Constraint.(lhs constr, rhs constr) in
    Settings.if_debug (fun () ->
        Format.printf "Checking constraint %a\n" Constraint.pp (Constraint.make lhs rhs)
    );
    let tags =
        StringSet.union (Pattern.tags lhs) (Pattern.tags rhs)
        |> StringSet.elements in
    (tags, SemiLinearSet.of_pattern lhs, SemiLinearSet.of_pattern rhs)

(* Encodes the inclusion as a Presburger goal, for the benefit of backends that
   want a formula rather than the semilinear sets themselves. *)
let semilinear_to_goal (tags, semilinear_lhs, semilinear_rhs) =
    let presburger_lhs = semilinear_to_presburger tags semilinear_lhs in
    let presburger_rhs = semilinear_to_presburger tags semilinear_rhs in
    Presburger.make_goal tags presburger_lhs presburger_rhs

(* Given a set of resolved lower bounds (i.e., mappings from pattern variables
   to closed formule) and a set of upper bounds (i.e., formulae where the RHS
   contains no pattern variables), ensure that the inclusions hold.
 *)
let check_satisfiability resolved_lowers =

    (* [goal] is lazy: only the Z3 backend needs the Presburger encoding, and we
       otherwise touch it only when reporting under --debug. *)
    let check_result constr goal =
        let open Format in
        let open Solver_result in
        let (lhs, rhs) = Constraint.((lhs constr, rhs constr)) in
        let (lhs, rhs) = Pattern.((show lhs, show rhs)) in
        function
            | Satisfiable ->
                Settings.if_debug (fun () ->
                    printf "SATISFIABLE: %a\n" Presburger.pp_goal (Lazy.force goal))
            | Unsatisfiable ->
                Settings.if_debug (fun () ->
                    printf "UNSATISFIABLE: %a\n" Presburger.pp_goal (Lazy.force goal)
                );
                raise (Errors.constraint_solver_error lhs rhs)
            | Unknown ->
                Settings.if_debug (fun () ->
                    printf "DUNNO: %a\n" Presburger.pp_goal (Lazy.force goal)
                );
                raise (Errors.constraint_solver_error lhs rhs)
    in

    (* For each upper bound:
        1) Substitute each variable for the associated resolved lower bound on
            the LHS
        2) Simplify
        3) Translate into a semilinear set
        4) Translate into a Presburger formula
        5) Check validity
     *)
    (* Runs the native solver, falling back to Z3 on the goals it declines. *)
    let native_with_fallback (tags, lhs, rhs) goal =
        match Native_solver.solve tags lhs rhs with
            | Some result -> result
            | None -> Z3_solver.solve (Lazy.force goal)
    in

    (* Runs both backends and reports any disagreement, but defers to Z3 so that
       turning the comparison on cannot change whether a program typechecks. *)
    let compare_backends (tags, lhs, rhs) goal =
        let z3_result = Z3_solver.solve (Lazy.force goal) in
        let () =
            match Native_solver.solve tags lhs rhs with
                | None ->
                    Format.printf "SOLVER COMPARISON: native solver declined %a\n"
                        Presburger.pp_goal (Lazy.force goal)
                | Some native_result when native_result <> z3_result ->
                    Format.printf
                        "SOLVER MISMATCH: z3 said %a, native said %a for %a\n"
                        Solver_result.pp z3_result
                        Solver_result.pp native_result
                        Presburger.pp_goal (Lazy.force goal)
                | Some _ -> ()
        in
        z3_result
    in

    List.iter (
        fun constr ->
           let resolved_constr = resolve_constraint resolved_lowers constr in
           let semilinear = constraint_to_semilinear resolved_constr in
           (* The Presburger encoding is only needed by the Z3 backend, and
              building it is not free, so keep it lazy. *)
           let goal = lazy (semilinear_to_goal semilinear) in
           let result =
               match Settings.(get solver_backend) with
                   | Settings.SolverBackend.Z3 -> Z3_solver.solve (Lazy.force goal)
                   | Settings.SolverBackend.Native ->
                       native_with_fallback semilinear goal
                   | Settings.SolverBackend.Compare ->
                       compare_backends semilinear goal
           in
           check_result resolved_constr goal result
    )

(* Ensure that none of the patterns are resolved as zero. The type system is only
   sound if a solution is *usable* (i.e., nonzero).
   A pattern will typically only be resolved as zero if there is insufficient type
    information (for example, only a part of a program has been written), and an
    annotation has not been given.
 *)
let check_nonzero =
    PVarMap.iter (fun var pat ->
        if Pattern.is_zero pat then
            raise (Errors.constraint_solver_zero_error var))

(* Main pipeline *)
let pipeline constrs =
    Settings.if_verbose (fun () ->
        Format.printf "=== Input constraints ===\n%a\n\n"
            Constraint_set.pp constrs;
    );
    let pat_vars = Constraint_set.pattern_variables constrs in
    let constrs = Constraint_set.elements constrs in
    (* Begin by getting all lower bounds (i.e., pattern variable on RHS) *)
    let resolved_constraints =
        let lbs =
            get_lower_bounds constrs
            |> group_lower_bounds pat_vars
        in
        Settings.if_debug (fun () ->
            Printf.printf "Grouped lower bounds:\n";
            PVarMap.iter (fun k p ->
                Format.(fprintf std_formatter "%s: %a\n" k Pattern.pp p)
            ) lbs
        );
        (* Compute solutions of patterns, and substitute through in order
           to rid ourselves of pattern variables *)
        substitute_solutions lbs
    in
    Settings.if_debug (fun () ->
        Printf.printf "=== Simplified constraint set ===\n\n";
        PVarMap.iter (fun k p ->
            Format.(fprintf std_formatter "%s: %a\n" k Pattern.pp p)
        ) resolved_constraints
    );
    (* Check if solutions are satisfiable *)
    check_satisfiability resolved_constraints (get_upper_bounds constrs);
    (* Ensure that none of the pattern variables have been solved as zero *)
    check_nonzero resolved_constraints;
    resolved_constraints

(* External API *)
let solve_constraints = pipeline

