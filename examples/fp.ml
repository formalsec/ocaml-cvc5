(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

(* Example taken from:
   https://github.com/florianschanda/smtlib_schanda/blob/master/crafted/QF_FP/assoc_1.smt2 *)

open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver ~logic:"QF_FP" tm

let fp_sort = Sort.mk_fp_sort tm 8 24

let rm_sort = Sort.mk_rm_sort tm

let x = Term.mk_const_s tm fp_sort "x"

let y = Term.mk_const_s tm fp_sort "y"

let z = Term.mk_const_s tm fp_sort "z"

let rm = Term.mk_const_s tm rm_sort "rm"

let () =
  let bv_one = Term.mk_bv_s tm 32 "1" 10 in
  let bv_zero = Term.mk_bv_s tm 32 "0" 10 in

  let fp_one = Term.mk_fp tm 8 24 bv_one in
  let fp_zero = Term.mk_fp tm 8 24 bv_zero in

  let rne = Term.mk_rm tm RoundingMode.Rne in

  let to_fp = Op.mk_op tm Kind.Floatingpoint_to_fp_from_fp [| 8; 24 |] in

  Printf.printf "op: %s\n" (Op.to_string to_fp);

  let t1 =
    Term.mk_term tm Kind.Floatingpoint_eq
      [| Term.mk_term tm Kind.Floatingpoint_add
           [| rm; x; Term.mk_term tm Kind.Floatingpoint_add [| rm; y; z |] |]
       ; Term.mk_term_op tm to_fp [| rne; fp_zero |]
      |]
  in

  let t2 =
    Term.mk_term tm Kind.Floatingpoint_eq
      [| Term.mk_term tm Kind.Floatingpoint_add
           [| rm; Term.mk_term tm Kind.Floatingpoint_add [| rm; x; y |]; z |]
       ; Term.mk_term_op tm to_fp [| rne; fp_one |]
      |]
  in

  Printf.printf "t1: %s\n" (Term.to_string t1);
  Printf.printf "t2: %s\n" (Term.to_string t2);

  Solver.assert_formula solver t1;
  Solver.assert_formula solver t2;
  let r = Solver.check_sat solver in

  match Result.is_sat r with
  | true -> Printf.printf "sat\n"
  | false -> Printf.printf "unsat\n"
