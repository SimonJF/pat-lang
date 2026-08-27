(* Tests for the native inclusion solver.

   The solver is checked against a brute-force oracle rather than against Z3.
   Two reasons: the oracle is independent of the machinery under test, and Z3
   as the typechecker configures it turns out to be the less reliable of the
   two -- [run_z3_comparison] measures exactly that.

   The oracle works because the counterexample direction can be verified
   exactly. Deciding whether a specific vector belongs to a linear set is a
   terminating search -- every period is nonzero, so each coefficient is bounded
   by the vector it has to build -- and the solver hands us the vector it
   objected to. For the other direction we hunt for a counterexample by
   enumeration up to a bound: not a proof of inclusion, but enough to catch a
   solver that wrongly claims one.
*)
open Typecheck
open Semilinear

let failures = ref 0

let report fmt = Format.kasprintf (fun s -> incr failures; print_endline s) fmt

(* --- Building semilinear sets by hand ------------------------------------ *)

let bag tags counts =
    List.fold_left2
        (fun acc tag n -> if n = 0 then acc else TagBag.add tag ~mult:n acc)
        TagBag.empty tags counts

let linear tags base periods =
    (bag tags base, PeriodSet.of_list (List.map (bag tags) periods))

let semilinear tags linsets =
    SemiLinearSet.of_list (List.map (fun (b, ps) -> linear tags b ps) linsets)

let pp_set = SemiLinearSet.pp

let pp_vec ppf v =
    Format.fprintf ppf "(%s)"
        (String.concat ", " (Array.to_list (Array.map string_of_int v)))

(* --- Brute-force oracle -------------------------------------------------- *)

(* Deliberately a separate implementation from [Native_solver.vectorise], so
   that a bug there cannot hide itself from the oracle. *)
let vectorise tags sls =
    let of_bag b = Array.of_list (List.map (fun t -> TagBag.occ t b) tags) in
    SemiLinearSet.elements sls
    |> List.map (fun (base, periods) ->
        (of_bag base,
         PeriodSet.elements periods
         |> List.map of_bag
         |> List.filter (Array.exists (fun x -> x <> 0))))

let nonneg = Array.for_all (fun x -> x >= 0)

(* Is [v] in the linear set with the given base and periods? Subtract the base,
   then try every coefficient for each period in turn. The search terminates
   because periods are nonzero and residuals must stay non-negative. *)
let in_linear v (base, periods) =
    let residual = Array.mapi (fun i x -> x - base.(i)) v in
    nonneg residual
    &&
    let rec search residual = function
        | [] -> Array.for_all (fun x -> x = 0) residual
        | period :: rest ->
            let rec try_coefficients residual =
                search residual rest
                || (let next = Array.mapi (fun i x -> x - period.(i)) residual in
                    nonneg next && try_coefficients next)
            in
            try_coefficients residual
    in
    search residual periods

let in_set v linsets = List.exists (in_linear v) linsets

(* Searches for a vector in [lhs] but not [rhs], with every component at most
   [bound]. *)
let brute_force_counterexample k bound lhs rhs =
    let found = ref None in
    let rec enumerate i acc =
        if !found = None then
            if i = k then begin
                let v = Array.of_list (List.rev acc) in
                if in_set v lhs && not (in_set v rhs) then found := Some v
            end else
                for x = 0 to bound do
                    enumerate (i + 1) (x :: acc)
                done
    in
    enumerate 0 [];
    !found

(* --- Checking one inclusion against the oracle --------------------------- *)

let brute_force_bound = 24

let check_against_oracle tags lhs rhs =
    let k = List.length tags in
    let lhs_v = vectorise tags lhs and rhs_v = vectorise tags rhs in
    match Native_solver.check_inclusion tags lhs rhs with
        | exception Native_solver.Gave_up reason ->
            report "DECLINED (%s): %a in %a" reason pp_set lhs pp_set rhs
        | Some counterexample ->
            (* The solver says the inclusion fails. Its witness is checkable
               exactly, so this direction is fully verified. *)
            let v =
                Array.of_list
                    (List.map
                        (fun tag ->
                            Option.value ~default:0
                                (List.assoc_opt tag counterexample))
                        tags)
            in
            if not (in_set v lhs_v) then
                report "BAD WITNESS: %a is not in %a" pp_vec v pp_set lhs
            else if in_set v rhs_v then
                report "BAD WITNESS: %a is in %a after all" pp_vec v pp_set rhs
        | None ->
            (* The solver says the inclusion holds. Try to refute it. *)
            (match brute_force_counterexample k brute_force_bound lhs_v rhs_v with
                | None -> ()
                | Some v ->
                    report "MISSED: %a in %a -- solver said it holds, but %a is \
                            in the left and not the right"
                        pp_set lhs pp_set rhs pp_vec v)

(* --- Regressions --------------------------------------------------------- *)

(* Each case is (tags, lhs, rhs, does the inclusion hold?). *)
let regressions = [
    (* The shape that defeats the obvious syntactic check: {4,5,6,...} is
       contained in {0,2,3,4,...} even though the left period 1 is not in the
       monoid generated by {2,3}. Anything reasoning only about generators gets
       this wrong. *)
    (["A"], [([4], [[1]])], [([0], [[2]; [3]])], true);
    (* ...and the same target really does miss 1, so this one fails. *)
    (["A"], [([0], [[1]])], [([0], [[2]; [3]])], false);

    (* Plain periodicity. *)
    (["A"], [([0], [[2]])], [([0], [[1]])], true);
    (["A"], [([0], [[1]])], [([0], [[2]])], false);

    (* Covering a period by a union of shifted copies: the evens and the odds
       together are everything. *)
    (["A"], [([0], [[1]])], [([0], [[2]]); ([1], [[2]])], true);
    (["A"], [([0], [[1]])], [([0], [[2]]); ([1], [[4]])], false);

    (* Degenerate sets. *)
    (["A"], [], [([0], [])], true);           (* empty is in anything *)
    (["A"], [([0], [])], [], false);          (* nothing is in empty *)
    (["A"], [([0], [])], [([0], [])], true);  (* the zero multiset *)

    (* Several tags, with periods that move more than one at a time. *)
    (["A"; "B"], [([1; 1], [[1; 1]])], [([0; 0], [[1; 1]])], true);
    (["A"; "B"], [([0; 0], [[1; 1]])], [([1; 1], [[1; 1]])], false);
    (["A"; "B"], [([2; 0], [[1; 0]])], [([0; 0], [[1; 0]; [0; 1]])], true);
    (["A"; "B"], [([0; 0], [[1; 0]; [0; 1]])], [([0; 0], [[1; 1]])], false);

    (* Independent tags: a period on one must not licence the other. *)
    (["A"; "B"], [([0; 0], [[2; 0]])], [([0; 0], [[1; 0]])], true);
    (["A"; "B"], [([0; 0], [[0; 2]])], [([0; 0], [[1; 0]])], false);

    (* Found by fuzzing. The inclusion fails -- the left contains (3, 3), which
       none of the three linear sets on the right can produce -- but Z3's "qe"
       tactic reports it as holding, with or without a timeout. Kept as a
       regression because it is the case that first showed the tactic pipeline
       the typechecker uses is unsound. *)
    (["A"; "B"],
     [([0; 0], [[1; 1]]); ([1; 0], [[1; 0]]); ([2; 2], [])],
     [([0; 0], [[1; 0]; [1; 2]]); ([1; 1], []); ([1; 3], [[1; 2]; [3; 2]])],
     false);
]

let run_regressions () =
    List.iter
        (fun (tags, lhs, rhs, expected) ->
            let lhs = semilinear tags lhs and rhs = semilinear tags rhs in
            let expected =
                if expected then Solver_result.Satisfiable
                else Solver_result.Unsatisfiable
            in
            (match Native_solver.solve tags lhs rhs with
                | None -> report "DECLINED: %a in %a" pp_set lhs pp_set rhs
                | Some actual when actual <> expected ->
                    report "WRONG: %a in %a -- expected %a, got %a"
                        pp_set lhs pp_set rhs
                        Solver_result.pp expected Solver_result.pp actual
                | Some _ -> ());
            check_against_oracle tags lhs rhs)
        regressions

(* --- Fuzzing ------------------------------------------------------------- *)

let random_semilinear tags =
    let count () = Random.int 4 in
    let vec () = List.map (fun _ -> count ()) tags in
    let nonzero v = List.exists (fun x -> x <> 0) v in
    let periods () =
        List.init (Random.int 3) (fun _ -> vec ()) |> List.filter nonzero
    in
    semilinear tags
        (List.init (1 + Random.int 3) (fun _ -> (vec (), periods ())))

let fuzz_cases iterations =
    let all_tags = ["A"; "B"; "C"] in
    List.init iterations (fun _ ->
        let tags = List.filteri (fun i _ -> i < 1 + Random.int 3) all_tags in
        (tags, random_semilinear tags, random_semilinear tags))

let time name f =
    let start = Unix.gettimeofday () in
    let result = f () in
    Printf.printf "%-28s %6.2fs\n%!" name (Unix.gettimeofday () -. start);
    result

let run_fuzz cases =
    List.iter (fun (tags, lhs, rhs) -> check_against_oracle tags lhs rhs) cases

(* --- How the Z3 backend compares ----------------------------------------- *)

(* Informational rather than pass/fail: runs the same goals through the tactic
   pipeline the typechecker uses and reports how often it declines to answer or
   contradicts the oracle-checked native result. *)
let run_z3_comparison cases =
    let unknown = ref 0 and disagree = ref 0 and total = ref 0 in
    List.iter
        (fun (tags, lhs, rhs) ->
            match Native_solver.solve tags lhs rhs with
                | None -> ()
                | Some native ->
                    incr total;
                    let goal =
                        Solve_constraints.semilinear_to_goal (tags, lhs, rhs)
                    in
                    (match Z3_solver.solve goal with
                        | Solver_result.Unknown -> incr unknown
                        | z3 when z3 <> native ->
                            incr disagree;
                            Format.printf
                                "z3 disagrees: %a in %a -- z3 %a, native %a\n"
                                pp_set lhs pp_set rhs
                                Solver_result.pp z3 Solver_result.pp native
                        | _ -> ()))
        cases;
    Printf.printf
        "z3 (qe + qflia) on %d goals: %d unknown, %d disagreements\n"
        !total !unknown !disagree

let () =
    Random.self_init ();
    run_regressions ();
    let iterations =
        Option.value ~default:2000
            (Option.bind (Sys.getenv_opt "PAT_FUZZ") int_of_string_opt)
    in
    let cases = fuzz_cases iterations in
    time (Printf.sprintf "native + oracle (%d goals)" iterations)
        (fun () -> run_fuzz cases);
    if Sys.getenv_opt "PAT_SKIP_Z3" = None then
        time (Printf.sprintf "z3 comparison (%d goals)" iterations)
            (fun () -> run_z3_comparison cases);
    if !failures = 0 then print_endline "solver: all checks passed"
    else (Printf.printf "solver: %d failure(s)\n" !failures; exit 1)
