(* SJF: This file is entirely Claude-written. It's a prototype specialised solver
   for the particular shape of inclusion constraints we generate from solve_constraints
   and is pure OCaml, with the goal of serving as a backend that does not
   require Z3 as a dependency (thus allowing it to be used as part of an online
   playground).
   
   It is opaque, not mine, I don't understand it, and so it's unsupported, but I
   must admit I'm pretty gobsmacked.
   ====
 *)

(* A native decision procedure for the inclusions produced by
   [Solve_constraints], written so that no external solver is required.

   Every goal we ship to Z3 has the same shape: given a set of tags, does one
   semilinear set contain another? Translating that into a Presburger formula
   and asking for general quantifier elimination throws away the structure we
   started with, so instead we decide the inclusion directly.

   The encoding is the classical one for Presburger-definable sets. Fix an
   ordering on the k tags, and encode a vector of tag counts least-significant
   -bit-first as a word over the alphabet {0,1}^k. Under this encoding the
   linear set

       L(c, {q_1, ..., q_m}) = { t | exists mu >= 0. t_i = c_i + sum_j q_j[i].mu_j }

   is recognised by a finite automaton. Its states are the residuals of the
   defining system of k equations: reading one column of bits consumes the
   lowest bit of every variable and halves what remains to be satisfied. The
   period variables mu_j are existentially quantified, so we project them out
   during the construction by guessing their bits, which keeps the alphabet at
   2^k rather than 2^(k+m).

   Inclusion of semilinear sets is then language inclusion of the two automata.
   We determinise the right-hand one and search the product for a word the left
   accepts and the right rejects. Such a word decodes to a concrete multiset of
   messages: a counterexample witnessing why the inclusion fails.

   Two properties make this sound. First, the automaton for a system of
   equations accepts a word exactly when the vector it denotes satisfies the
   system, so acceptance depends only on the vector and not on the choice of
   encoding (in particular, trailing zeroes are harmless). Language inclusion
   and inclusion of the denoted sets therefore coincide. Second, the residuals
   are bounded: if |s| <= max(|c_i|, 1 + sum_j q_j[i]) then the successor
   residual satisfies the same bound, so the state space is finite and the
   construction terminates.
*)

(* Raised when a construction exceeds its limit. The goals arising from real
   programs are small; these bounds exist so that a pathological constraint
   degrades to a fallback rather than hanging. *)
exception Gave_up of string

let max_tags = 14
let max_nfa_states = 50000
let max_dfa_states = 50000

module ISet = Set.Make(Int)

(* A vector of tag counts, indexed by position in the tag ordering. *)
type vec = int array

type nfa = {
    initial : int list;
    accepting : bool array;
    delta : int list array array (* delta.(state).(letter) *)
}

type dfa = {
    d_initial : int;
    d_accepting : bool array;
    d_delta : int array array (* d_delta.(state).(letter) *)
}

(* Projects a semilinear set onto the given tag ordering, giving each linear set
   as a base vector and a list of period vectors. Zero periods are dropped: they
   contribute nothing, and every one we discard halves the work done when
   guessing period bits. *)
let vectorise tags sls : (vec * vec list) list =
    let open Semilinear in
    let of_bag bag = Array.of_list (List.map (fun t -> TagBag.occ t bag) tags) in
    let nonzero v = Array.exists (fun x -> x <> 0) v in
    SemiLinearSet.elements sls
    |> List.map (fun (base, periods) ->
        (of_bag base,
         PeriodSet.elements periods |> List.map of_bag |> List.filter nonzero))

(* Builds the automaton recognising the union of the given linear sets.

   A state is a linear set index paired with the residuals of that set's
   equations, so the disjunction is handled simply by starting in every base at
   once. Reading letter [alpha] with a guess [gamma] for the low bits of the
   period variables leaves residual (s_i - d_i) / 2 for

       d_i = alpha_i - sum_j q_j[i].gamma_j

   and is possible only when every s_i - d_i is even. *)
let build_nfa k (linsets : (vec * vec list) list) : nfa =
    let linsets = Array.of_list linsets in
    let nletters = 1 lsl k in
    let ids : (int * vec, int) Hashtbl.t = Hashtbl.create 256 in
    let count = ref 0 in
    let queue = Queue.create () in
    let intern key =
        match Hashtbl.find_opt ids key with
            | Some id -> id
            | None ->
                let id = !count in
                if id >= max_nfa_states then
                    raise (Gave_up "automaton exceeded state limit");
                Hashtbl.add ids key id;
                incr count;
                Queue.add (id, key) queue;
                id
    in
    let initial =
        Array.to_list linsets |> List.mapi (fun i (base, _) -> intern (i, base))
    in
    let trans = Hashtbl.create 256 in
    while not (Queue.is_empty queue) do
        let (id, (li, residual)) = Queue.pop queue in
        let periods = Array.of_list (snd linsets.(li)) in
        let m = Array.length periods in
        let row = Array.make nletters [] in
        for letter = 0 to nletters - 1 do
            let targets = ref [] in
            for gamma = 0 to (1 lsl m) - 1 do
                let next = Array.make k 0 in
                let feasible = ref true in
                let t = ref 0 in
                while !feasible && !t < k do
                    let d = ref ((letter lsr !t) land 1) in
                    for j = 0 to m - 1 do
                        if (gamma lsr j) land 1 = 1 then
                            d := !d - periods.(j).(!t)
                    done;
                    let r = residual.(!t) - !d in
                    (* [land 1] rather than [mod 2]: the residual may be
                       negative, and we want the parity, not the remainder. *)
                    if r land 1 <> 0 then feasible := false
                    else next.(!t) <- r / 2;
                    incr t
                done;
                if !feasible then begin
                    let target = intern (li, next) in
                    if not (List.mem target !targets) then
                        targets := target :: !targets
                end
            done;
            row.(letter) <- !targets
        done;
        Hashtbl.replace trans id row
    done;
    let n = !count in
    let delta = Array.make n [||] in
    Hashtbl.iter (fun id row -> delta.(id) <- row) trans;
    let accepting = Array.make n false in
    Hashtbl.iter
        (fun (_, residual) id ->
            accepting.(id) <- Array.for_all (fun x -> x = 0) residual)
        ids;
    { initial; accepting; delta }

(* Subset construction. The empty set arises naturally and acts as the sink, so
   the result is complete and can be complemented by negating [d_accepting]. *)
let determinise k (nfa : nfa) : dfa =
    let nletters = 1 lsl k in
    let ids : (ISet.t, int) Hashtbl.t = Hashtbl.create 256 in
    let count = ref 0 in
    let queue = Queue.create () in
    let intern set =
        match Hashtbl.find_opt ids set with
            | Some id -> id
            | None ->
                let id = !count in
                if id >= max_dfa_states then
                    raise (Gave_up "determinisation exceeded state limit");
                Hashtbl.add ids set id;
                incr count;
                Queue.add (id, set) queue;
                id
    in
    let d_initial = intern (ISet.of_list nfa.initial) in
    let trans = Hashtbl.create 256 in
    while not (Queue.is_empty queue) do
        let (id, set) = Queue.pop queue in
        let row = Array.make nletters 0 in
        for letter = 0 to nletters - 1 do
            let target =
                ISet.fold
                    (fun s acc ->
                        List.fold_left (fun acc t -> ISet.add t acc)
                            acc nfa.delta.(s).(letter))
                    set ISet.empty
            in
            row.(letter) <- intern target
        done;
        Hashtbl.replace trans id row
    done;
    let n = !count in
    let d_delta = Array.make n [||] in
    Hashtbl.iter (fun id row -> d_delta.(id) <- row) trans;
    let d_accepting = Array.make n false in
    Hashtbl.iter
        (fun set id ->
            d_accepting.(id) <- ISet.exists (fun s -> nfa.accepting.(s)) set)
        ids;
    { d_initial; d_accepting; d_delta }

(* Searches the product of [lhs] (nondeterministic) with [rhs] (a complete DFA)
   for a word the former accepts and the latter rejects.

   Following a single nondeterministic run of [lhs] alongside the unique run of
   [rhs] is enough: reaching an accepting [lhs] state witnesses membership, and
   the [rhs] component is the only run there is on that word. Breadth-first
   search gives the shortest such word, which decodes to the smallest
   counterexample. *)
let find_counterexample k (lhs : nfa) (rhs : dfa) : vec option =
    let nletters = 1 lsl k in
    let parents = Hashtbl.create 256 in
    let queue = Queue.create () in
    let push parent letter state =
        if not (Hashtbl.mem parents state) then begin
            Hashtbl.add parents state (parent, letter);
            Queue.add state queue
        end
    in
    List.iter (fun a -> push None 0 (a, rhs.d_initial)) lhs.initial;
    let witness = ref None in
    (try
        while not (Queue.is_empty queue) do
            let (a, b) as state = Queue.pop queue in
            if lhs.accepting.(a) && not rhs.d_accepting.(b) then begin
                witness := Some state;
                raise Exit
            end;
            for letter = 0 to nletters - 1 do
                let b' = rhs.d_delta.(b).(letter) in
                List.iter
                    (fun a' -> push (Some state) letter (a', b'))
                    lhs.delta.(a).(letter)
            done
        done
    with Exit -> ());
    (* Walk the parent chain back to an initial state, collecting the letters.
       Reversing puts them back in reading order, so the letter at index p
       carries the bits of weight 2^p. *)
    Option.map
        (fun state ->
            let rec collect acc state =
                match Hashtbl.find parents state with
                    | None, _ -> acc
                    | Some parent, letter -> collect (letter :: acc) parent
            in
            let letters = collect [] state in
            let counts = Array.make k 0 in
            List.iteri
                (fun p letter ->
                    for t = 0 to k - 1 do
                        counts.(t) <- counts.(t) + (((letter lsr t) land 1) lsl p)
                    done)
                letters;
            counts)
        !witness

(* Decides whether [lhs] is contained in [rhs]. Returns [None] if it is, and
   otherwise a multiset of tags that [lhs] permits but [rhs] does not.
   Raises [Gave_up] if a construction exceeds its limit. *)
let check_inclusion tags lhs rhs : (string * int) list option =
    let k = List.length tags in
    if k > max_tags then
        raise (Gave_up (Printf.sprintf "%d tags exceeds the limit of %d" k max_tags));
    let lhs_linsets = vectorise tags lhs and rhs_linsets = vectorise tags rhs in
    let lhs = build_nfa k lhs_linsets in
    let rhs_nfa = build_nfa k rhs_linsets in
    let rhs = determinise k rhs_nfa in
    Common.Settings.if_debug (fun () ->
        Printf.printf
            "NATIVE: %d tags, %d/%d linear sets, %d/%d nfa states, %d dfa states\n"
            k (List.length lhs_linsets) (List.length rhs_linsets)
            (Array.length lhs.accepting) (Array.length rhs_nfa.accepting)
            (Array.length rhs.d_accepting));
    find_counterexample k lhs rhs
    |> Option.map (fun counts ->
        List.mapi (fun i tag -> (tag, counts.(i))) tags
        |> List.filter (fun (_, n) -> n > 0))

let pp_counterexample ppf =
    let open Format in
    function
        | [] -> pp_print_string ppf "⟨⟩"
        | tags ->
            let pp_entry ppf (tag, n) = fprintf ppf "%s ⨉ %d" tag n in
            fprintf ppf "⟨%a⟩"
                (Util.Utility.pp_print_comma_list pp_entry) tags

(* The solver interface, mirroring [Z3_solver.solve]. [Satisfiable] means the
   inclusion holds. Returns [None] if the goal fell outside our limits, so that
   the caller can fall back to another backend. *)
let solve tags lhs rhs : Solver_result.t option =
    try
        match check_inclusion tags lhs rhs with
            | None -> Some Solver_result.Satisfiable
            | Some counterexample ->
                Common.Settings.if_debug (fun () ->
                    Format.printf "NATIVE COUNTEREXAMPLE: %a\n"
                        pp_counterexample counterexample);
                Some Solver_result.Unsatisfiable
    with Gave_up reason ->
        Common.Settings.if_debug (fun () ->
            Printf.printf "NATIVE SOLVER GAVE UP: %s\n" reason);
        None
