open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let int_sort = Sort.mk_int_sort tm

let () =
  let fun_sort = Sort.mk_function_sort tm [| int_sort |] int_sort in
  let f = Term.mk_const_s tm fun_sort "f" in
  let x = Term.mk_const_s tm int_sort "x" in
  let app = Term.mk_term tm Kind.Apply_uf [| f; x |] in
  let zero = Term.mk_int tm 0 in
  let constraint_t = Term.mk_term tm Kind.Gt [| app; zero |] in
  Solver.assert_formula solver constraint_t;
  let result = Solver.check_sat solver in
  assert (Result.is_sat result);
  print_endline "PASS: function_sort + mk_const + Apply_uf works"
