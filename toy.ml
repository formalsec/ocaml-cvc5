open Cvc5_cxx.Cvc5_external

let tm = new_term_manager ()

let solver = new_solver tm

let _true_term = mk_true tm

let false_term = mk_false tm

let () =
  ignore (assert_formula solver false_term);
  let r = check_sat solver in
  let b = result_is_sat r tm in
  match b with
  | true -> print_endline "sat OCaml"
  | false -> print_endline "unsat OCaml"
