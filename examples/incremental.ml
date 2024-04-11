open Cvc5

let start_val = 0

let end_val = 1000

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let int_sort = Sort.mk_int_sort tm

let x = Term.mk_const_s tm int_sort "x"

(* Example with incremental use of the solver *)
let () =
  for i = start_val to end_val do
    let i_term = Term.mk_int tm i in
    (* Create new formula: x > i, where i is the loop's counter *)
    let x_gt_i = Term.mk_term tm Kind.Gt [| x; i_term |] in
    Printf.printf "Asserting: %s\n" (Term.to_string x_gt_i);
    Solver.assert_formula solver x_gt_i;
    (* Push new context *)
    Solver.push solver 1
  done;

  let r = Solver.check_sat solver in
  match Result.is_sat r with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n"
