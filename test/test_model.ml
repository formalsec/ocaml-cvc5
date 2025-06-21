(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let () = Solver.set_option solver "produce-models" "true"

let int_sort = Sort.mk_int_sort tm

let zero = Term.mk_int tm 0

let one = Term.mk_int tm 1

let x = Term.mk_const_s tm int_sort "x"

let y = Term.mk_const_s tm int_sort "y"

let x_eq_zero = Term.mk_term tm Kind.Equal [| x; zero |]

let y_gt_one = Term.mk_term tm Kind.Gt [| y; one |]

let () =
  Solver.assert_formula solver x_eq_zero;
  Solver.assert_formula solver y_gt_one;
  ignore (Solver.check_sat solver);
  (* check if model matches expected solution *)
  let sol = [| (x, 0); (y, 2) |] in
  Array.iter
    (fun (t, v) ->
      let v' = Solver.get_value solver t in
      let i = Term.get_int v' in
      assert (i = v) )
    sol
