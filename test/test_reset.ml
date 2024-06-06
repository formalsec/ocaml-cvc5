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

(* Reset the assertions of a solver and checking its satisfiability should produce SAT *)
let () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let false_const = Term.mk_false tm in
  Solver.assert_formula solver false_const;
  Solver.reset solver;
  let result = Solver.check_sat solver in
  assert (Result.is_sat result)
