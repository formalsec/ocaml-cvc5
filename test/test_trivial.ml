(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5

(* A formula with logical value true should produce SAT *)
let () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let true_const = Term.mk_true tm in
  Solver.assert_formula solver true_const;
  let result = Solver.check_sat solver in
  assert (Result.is_sat result)
