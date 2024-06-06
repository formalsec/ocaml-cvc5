(**************************************************************************)
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
(**************************************************************************)

open Cvc5

let start_val = 0

let end_val = 5000

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
    (* Printf.printf "Asserting: %s\n" (Term.to_string x_gt_i); *)
    Solver.assert_formula solver x_gt_i
    (* Push new context *)
    (* Solver.push solver 1 *)
  done;

  let r = Solver.check_sat solver in
  match Result.is_sat r with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n"
