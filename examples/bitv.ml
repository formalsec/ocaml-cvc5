(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

(* Example taken from:
   https://github.com/florianschanda/smtlib_schanda/blob/master/crafted/QF_BV/arith_2.smt2 *)

open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver ~logic:"QF_BV" tm

let bitv_sort = Sort.mk_bv_sort tm 9

let x = Term.mk_const_s tm bitv_sort "x"

let y = Term.mk_const_s tm bitv_sort "y"

let () =
  let a =
    Term.mk_term tm Bitvector_mult
      [| Term.mk_term tm Bitvector_add [| x; y |]
       ; Term.mk_term tm Bitvector_add [| x; y |]
      |]
  in

  let two = Term.mk_bv_s tm 9 "2" 10 in

  let b =
    Term.mk_term tm Bitvector_add
      [| Term.mk_term tm Bitvector_mult [| x; x |]
       ; Term.mk_term tm Bitvector_mult
           [| y
            ; Term.mk_term tm Bitvector_add
                [| Term.mk_term tm Bitvector_mult [| x; two |]; y |]
           |]
      |]
  in

  Printf.printf "a: %s\n" (Term.to_string a);
  Printf.printf "b: %s\n" (Term.to_string b);
  (* check satisfiability of a != b *)
  Solver.assert_formula solver (Term.mk_term tm Distinct [| a; b |]);
  let r = Solver.check_sat solver in

  match Result.is_sat r with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n"
