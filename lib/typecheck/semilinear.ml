(* Semilinear sets over multisets of message tags.

   A pattern (a commutative regular expression) denotes a set of multisets of
   tags. That set is always semilinear: a finite union of linear sets

       L(b, {p_1, ..., p_m}) = { b + k_1.p_1 + ... + k_m.p_m | k_j >= 0 }

   where the base b and the periods p_j are themselves multisets of tags. This
   module builds that representation; deciding inclusions between the resulting
   sets is left to the solver backends.
*)
open Common
open Util.Utility
open Type

module TagBag = Bag.Make(String)
module PeriodSet = Set.Make(TagBag)

type tag_multiset = TagBag.t

type base = tag_multiset
type period = tag_multiset

module LinearSet = struct
    type t = (base * PeriodSet.t)

    let compare (base1, periods1) (base2, periods2) =
        (* NOTE: We cannot use polymorphic comparisons on bags. *)
        (* While equality is pretty easy, having an ordering is quite strange. *)
        (* We use the following comparison:
            - If both base and periods are equal, return 0.
            - Compare bases. If nonzero, that's the result.
            - If zero, then use periods as a tiebreak.
         *)
        let base_cmp = TagBag.compare base1 base2 in
        let periods_cmp = PeriodSet.compare periods1 periods2 in
        if base_cmp = 0 then
            periods_cmp
        else
            base_cmp

    (* Unit linear set: empty bag and empty set of periods *)
    let one = (TagBag.empty, PeriodSet.empty)

    (* Singleton linear set: consists of a single tag *)
    let singleton tag = (TagBag.singleton tag, PeriodSet.empty)

    (* Product of linear sets: sum the multiplicities of the bases,
       and union the set of periods. *)
    let product (base1, periods1) (base2, periods2) =
        (TagBag.sum base1 base2, PeriodSet.union periods1 periods2)

    let pp ppf (base, period) =
        let open Format in

        let pp_multiset ppf ms =
            let pp_entry ppf (tag, n) =
                fprintf ppf "%s ⨉ %d" tag n
            in
            fprintf ppf "⟨%a⟩"
                (pp_print_comma_list pp_entry) (TagBag.elements ms)
        in

        let pp_multisets ppf =
            fprintf ppf "{ %a }" (pp_print_comma_list pp_multiset)
        in

        fprintf ppf "L(%a, %a)"
            pp_multiset base
            pp_multisets (PeriodSet.elements period)
end

module SemiLinearSet = struct
    include Set.Make(LinearSet)

    let one = singleton (LinearSet.one)

    (* Product of a semilinear set is the pointwise product of each constituent linear set *)
    let product sl1 sl2 =
        List.map (fun l1 ->
            List.map (fun l2 ->
                LinearSet.product l1 l2
            ) (elements sl2)
        ) (elements sl1)
        |> List.flatten
        |> of_list

    (* Replicates a linear set by 'promoting' the base to a period:
        L(C, P)* = { L(<>, {}) U L(C, {C} U P) }
    *)
    let replicate (base, periods) =
        let inner =
            (base, PeriodSet.union (PeriodSet.singleton base) periods)
        in
        of_list [LinearSet.one; inner]

    (* Translates a pattern (commutative regular expression) into a semilinear
       set. *)
    let rec of_pattern =
        let open Pattern in
        function
            | PatVar _ -> assert false (* HK resolution will have removed these. *)
            | One -> one
            | Zero -> empty
            | Message tag -> singleton (LinearSet.singleton tag)
            | Plus (p1, p2) -> union (of_pattern p1) (of_pattern p2)
            | Concat (p1, p2) -> product (of_pattern p1) (of_pattern p2)
            | Many p ->
                (* Replicate all linear sets produced by semantics of p.
                   This produces a list of semilinear sets. *)
                let sls_inner =
                    of_pattern p (* SemiLinearSet*)
                    |> elements (* [LinearSet]*)
                    |> List.map replicate (* [SemiLinearSet] *)
                in
                (* Concatenate them all using product *)
                List.fold_left product one sls_inner

    let pp ppf sls =
        let open Format in
        let pp_linset ppf = fprintf ppf "{ %a }" LinearSet.pp in
        pp_print_list ~pp_sep:(fun ppf () -> pp_print_string ppf " ∪ ")
            pp_linset ppf (elements sls)
end
