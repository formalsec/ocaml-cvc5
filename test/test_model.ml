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
