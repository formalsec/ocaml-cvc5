open Cvc5_cxx.Cvc5_external
open Cvc5_cxx.Kind

let tm = new_term_manager ()
let solver = new_solver tm
let _true_term = mk_true tm
let _false_term = mk_false tm
let _bool_sort = get_boolean_sort tm
let _int_sort = get_integer_sort tm
let x = mk_const tm _int_sort "x"
let zero = mk_int tm 0

let () =
  let x_gt_zero = mk_term tm (to_cpp Gt) [| x; zero |] in
  print_endline (term_to_string x_gt_zero);
  let x_lt_zero = mk_term tm (to_cpp Lt) [| x; zero |] in
  print_endline (term_to_string x_lt_zero);
  (* x > 0 *)
  assert_formula solver x_gt_zero;
  (* x < 0 *)
  assert_formula solver x_lt_zero;
  let r = check_sat solver in
  let b = result_is_sat r in
  delete solver;
  delete_term_manager tm;
  match b with
  | true -> print_endline "sat OCaml"
  | false -> print_endline "unsat OCaml"
