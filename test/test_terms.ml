(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let int_sort = Sort.mk_int_sort tm

let zero = Term.mk_int tm 0

let x = Term.mk_const_s tm int_sort "x"

let x_geq_zero = Term.mk_term tm Kind.Geq [| x; zero |]

(* x >= 0 and ~(~(x >= 0) should be considered equal terms after simplications *)
let () =
  let x_geq_zero_not = Term.mk_term tm Kind.Not [| x_geq_zero |] in
  let x_geq_zero_not_not = Term.mk_term tm Kind.Not [| x_geq_zero_not |] in
  let simplified = Solver.simplify solver x_geq_zero_not_not in
  assert (Term.equal x_geq_zero simplified)

(* Different terms should not be considered equal *)
let () =
  let false_const = Term.mk_false tm in
  assert (not (Term.equal false_const x_geq_zero))

(* Term.kind returns the correct Kind of a term *)
let () =
  assert (Term.kind x_geq_zero = Kind.Geq);
  assert (not (Term.kind x_geq_zero = Kind.Not))

(* Test checking the satisfiability with assumptions *)
let () =
  let x_lt_one = Term.mk_term tm Kind.Lt [| x; Term.mk_int tm 1 |] in
  Solver.assert_formula solver x_geq_zero;
  let result = Solver.check_sat_assuming solver [| x_lt_one |] in
  assert (Result.is_sat result)
