open Cvc5_cxx.Cvc5_external

let tm = new_term_manager ()

let solver = new_solver tm

let _true_term = mk_true tm

let false_term = mk_false tm

let bool_sort = get_boolean_sort tm

let _int_sort = get_integer_sort tm

let () =
  let st = mk_string tm "olaaaa" in
  let s = term_to_string st in
  print_endline s;
  ignore (assert_formula solver false_term);
  let r = check_sat solver in
  let b = result_is_sat r tm in
  let x = mk_const tm bool_sort "x" in
  print_endline (term_to_string x);
  ignore (bool_sort);
  ignore (delete solver);
  ignore (delete_term_manager tm);
  match b with
  | true -> print_endline "sat OCaml"
  | false -> print_endline "unsat OCaml"
