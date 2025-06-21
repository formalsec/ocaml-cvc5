(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5

(* This example demonstrates how to create a simple formulas and check their
   satisfiability. *)
let () =
  (* Create a TermManager *)
  let tm = TermManager.mk_tm () in
  (* Create a Solver *)
  let solver = Solver.mk_solver ~logic:"QF_UFLIA" tm in
  (* Set solver option to produce models *)
  Solver.set_option solver "produce-models" "true";
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

  (* Create an uninterpreted function that receives an argument with int_sort
     and returns a value with int_sort *)
  let uf = Solver.declare_fun solver "uf" [| int_sort |] int_sort in
  (* Apply the uninterpreted function to constant term 'x' -> uf(x) *)
  let x_uf = Term.mk_term tm Kind.Apply_uf [| uf; x |] in
  (* Create the term: uf(x) == 0 *)
  let x_uf_eq_zero = Term.mk_term tm Kind.Equal [| x_uf; zero |] in
  Printf.printf "Formula: %s\n" (Term.to_string x_uf_eq_zero);
  (* Assert the formula *)
  Solver.assert_formula solver x_uf_eq_zero;

  (* Obtain the satisfiability result of the asserted formulas *)
  let result = Solver.check_sat solver in
  ( match Result.is_sat result with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n" );

  (* Obtain the value for term 'x' *)
  let value = Solver.get_value solver x in
  Printf.printf "Value of x: %s\n" (Term.to_string value);

  (* Delete the TermManager and the Solver *)
  TermManager.delete tm;
  Solver.delete solver
