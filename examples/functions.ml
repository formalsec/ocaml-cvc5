(*------------------------------------------------------------------------*)
(*  Copyright (C) 2024 formalsec                                          *)
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

(* This example demonstrates how to create a simple formulas and check their
   satisfiability. *)
let () =
  (* Create a TermManager *)
  let tm = TermManager.mk_tm () in
  (* Create a Solver *)
  let solver = Solver.mk_solver ~logic:"ALL" tm in
  (* Set solver option to produce models *)
  Solver.set_option solver "produce-models" "true";
  (* Create an integer sort *)
  let int_sort = Sort.mk_int_sort tm in
  (* Create a free variable with integer sort *)
  let var = Term.mk_var_s tm int_sort "var" in
  (* Create an integer constant term 'x' *)
  let x = Term.mk_const_s tm int_sort "x" in
  (* Create an integer term with value 4 *)
  let four = Term.mk_int tm 4 in
  (* Create an integer term with value 2 *)
  let two = Term.mk_int tm 2 in

  (* Create the term: 2 * var.
     This term will be used as the body for the function we're going to define *)
  let body = Term.mk_term tm Kind.Mult [| two; var |] in
  (* Define a new function called "double" that has '2 * var' has a body and returns an integer *)
  let func = Solver.define_fun solver "double" [| var |] int_sort body in
  (* Apply the defined function to constant term 'x' *)
  let func_app = Term.mk_term tm Kind.Apply_uf [| func; x |] in

  (* Create a formula: double(x) = 4 *)
  let formula = Term.mk_term tm Kind.Equal [| func_app; four |] in
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
