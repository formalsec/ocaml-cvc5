open Cvc5

(* Reset the assertions of a solver and checking its satisfiability should produce SAT *)
let () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let false_const = Term.mk_false tm in
  Solver.assert_formula solver false_const;
  Solver.reset solver;
  let result = Solver.check_sat solver in
  assert (Result.is_sat result)
