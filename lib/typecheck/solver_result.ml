type t = | Satisfiable | Unsatisfiable | Unknown

let pp ppf =
    let open Format in
    function
        | Satisfiable -> pp_print_string ppf "satisfiable"
        | Unsatisfiable -> pp_print_string ppf "unsatisfiable"
        | Unknown -> pp_print_string ppf "unknown"
