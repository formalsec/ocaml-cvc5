(*------------------------------------------------------------------------*)
(*  Copyright (C) 2024 João Pereira                                       *)
(*                                                                        *)
(*  This file is part of ocaml-cvc5                                       *)
(*                                                                        *)
(*  ocaml-cvc5 is free software: you can redistribute it and/or modify    *)
(*  it under the terms of the GNU General Public License as published     *)
(*  by the Free Software Foundation, either version 3 of the License,     *)
(*  or (at your option) any later version.                                *)
(*                                                                        *)
(*  ocaml-cvc5 is distributed in the hope that it will be useful,         *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*  See the GNU General Public License for more details.                  *)
(*                                                                        *)
(*  You should have received a copy of the GNU General Public License     *)
(*  along with ocaml-cvc5. If not, see <http://www.gnu.org/licenses/>.    *)
(*------------------------------------------------------------------------*)

open Cvc5

(* This example demonstrates how to create a simple formula and check its
   satisfiability. *)
let () =
  (* Create a TermManager *)
  let tm = TermManager.mk_tm () in
  (* Create a Solver *)
  let solver = Solver.mk_solver tm in
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
