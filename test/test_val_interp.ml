(*------------------------------------------------------------------------*)
(*  Copyright (C) 2024 formalsec                                       *)
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

let tm = TermManager.mk_tm ()

(* Check int values construction and interpretation *)
let () =
  let one = Term.mk_int tm 1 in
  assert (Term.is_int one);
  assert (Term.get_int one = 1)

(* Check real values contruction and interpretation *)
let () =
  let one_float_s = Term.mk_real_s tm "1.0" in
  assert (Term.is_real one_float_s);
  assert (Term.get_real one_float_s = 1.0);

  let one_float_nd = Term.mk_real tm 1 2 in
  assert (Term.is_real one_float_nd);
  assert (Term.get_real one_float_nd = 0.5);

  let one_float_i = Term.mk_real_i tm 1 in
  assert (Term.is_real one_float_i);
  assert (Term.get_real one_float_i = 1.0)

(* Check boolean values construction and interpretation *)
let () =
  let true1 = Term.mk_bool tm true in
  assert (Term.is_bool true1);
  assert (Term.get_bool true1 = true);

  let true2 = Term.mk_true tm in
  assert (Term.is_bool true2);
  assert (Term.get_bool true2 = true)

(* Check string values construction and interpretation *)
let () =
  let str = Term.mk_string tm "abc" in
  assert (Term.is_string str);
  assert (Term.get_string str = "abc")

(* Check bit-vector values construction and interpretation *)
(* TODO *)
