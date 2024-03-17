open Cvc5_cxx.Cvc5_external

let tm = new_term_manager ()

let solver = new_solver tm

let t = mk_true tm

let () =
  ignore (assert_formula solver t);
  let r = check_sat solver in
  let b = result_is_sat r tm in
  match b with
  | true -> print_endline "sat OCaml"
  | false -> print_endline "unsat OCaml"
