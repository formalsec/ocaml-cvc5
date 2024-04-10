open Cvc5

(* This example demonstrates how to create a simple formula and check its
   satisfiability. *)
let () =
  (* Create a TermManager *)
  let tm = TermManager.mk_tm () in
  (* Create a Solver *)
  let solver = Solver.mk_solver tm in
  (* Create an integer sort *)
  let int_sort = Sort.mk_int_sort tm in
  (* Create an integer constant term 'x' *)
  let x = Term.mk_const_s tm int_sort "x" in
  (* Create an integer term with value 0 *)
  let zero = Term.mk_int tm 0 in

  (* Create the term: x >= 0 *)
  let x_gt_zero = Term.mk_term tm Kind.Geq [| x; zero |] in
  (* Create the term: x <= 0 *)
  let x_lt_zero = Term.mk_term tm Kind.Leq [| x; zero |] in
  (* Create a conjunction of both terms *)
  let formula = Term.mk_term tm Kind.And [| x_gt_zero; x_lt_zero |] in
  (* Print the created formula *)
  Printf.printf "Formula: %s\n" (Term.to_string formula);

  (* Assert the formula *)
  Solver.assert_formula solver formula;

  (* Obtain the satisfiability result of the asserted formulas *)
  let result = Solver.check_sat solver in
  ( match Result.is_sat result with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n" );

  (* Delete the TermManager and the Solver *)
  TermManager.delete tm;
  Solver.delete solver
