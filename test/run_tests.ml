(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5
open Alcotest

let is_true msg result = check bool msg true result

(* A formula with logical value true should produce SAT *)
let test_trivial () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let true_const = Term.mk_true tm in
  Solver.assert_formula solver true_const;
  let result = Solver.check_sat solver in
  is_true "is sat" (Result.is_sat result)

(* Test term simplification *)
let test_terms_simplification () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let int_sort = Sort.mk_int_sort tm in
  let zero = Term.mk_int tm 0 in
  let x = Term.mk_const_s tm int_sort "x" in
  let x_geq_zero = Term.mk_term tm Kind.Geq [| x; zero |] in
  let x_geq_zero_not = Term.mk_term tm Kind.Not [| x_geq_zero |] in
  let x_geq_zero_not_not = Term.mk_term tm Kind.Not [| x_geq_zero_not |] in
  (* x >= 0 and ~(~(x >= 0) should be considered equal terms after simplications *)
  let simplified = Solver.simplify solver x_geq_zero_not_not in
  is_true "term equal after simplification" (Term.equal x_geq_zero simplified)

(* Different terms should not be considered equal *)
let test_terms_not_equal () =
  let tm = TermManager.mk_tm () in
  let int_sort = Sort.mk_int_sort tm in
  let zero = Term.mk_int tm 0 in
  let x = Term.mk_const_s tm int_sort "x" in
  let x_geq_zero = Term.mk_term tm Kind.Geq [| x; zero |] in
  let false_const = Term.mk_false tm in
  is_true "different terms not equal" (not (Term.equal false_const x_geq_zero))

(* Term.kind returns the correct Kind of a term *)
let test_terms_kind () =
  let tm = TermManager.mk_tm () in
  let int_sort = Sort.mk_int_sort tm in
  let zero = Term.mk_int tm 0 in
  let x = Term.mk_const_s tm int_sort "x" in
  let x_geq_zero = Term.mk_term tm Kind.Geq [| x; zero |] in
  is_true "term kind is geq" (Term.kind x_geq_zero = Kind.Geq);
  is_true "term kind is not not" (not (Term.kind x_geq_zero = Kind.Not))

(* Test checking the satisfiability with assumptions *)
let test_terms_check_sat_assuming () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let int_sort = Sort.mk_int_sort tm in
  let zero = Term.mk_int tm 0 in
  let x = Term.mk_const_s tm int_sort "x" in
  let x_geq_zero = Term.mk_term tm Kind.Geq [| x; zero |] in
  let x_lt_one = Term.mk_term tm Kind.Lt [| x; Term.mk_int tm 1 |] in
  Solver.assert_formula solver x_geq_zero;
  let result = Solver.check_sat_assuming solver [| x_lt_one |] in
  is_true "check sat assuming is sat" (Result.is_sat result)

(* Check int values construction and interpretation *)
let test_val_interp_int () =
  let tm = TermManager.mk_tm () in
  let one = Term.mk_int tm 1 in
  is_true "is int" (Term.is_int one);
  check int "get int" 1 (Term.get_int one)

(* Check real values contruction and interpretation *)
let test_val_interp_real () =
  let one_float_s = Term.mk_real_s (TermManager.mk_tm ()) "1.0" in
  is_true "is real (s)" (Term.is_real one_float_s);
  check (float 0.0001) "get real (s)" 1.0 (Term.get_real one_float_s);

  let one_float_nd = Term.mk_real (TermManager.mk_tm ()) 1L 2L in
  is_true "is real (nd)" (Term.is_real one_float_nd);
  check (float 0.0001) "get real (nd)" 0.5 (Term.get_real one_float_nd);

  let one_float_i = Term.mk_real_i (TermManager.mk_tm ()) 1L in
  is_true "is real (i)" (Term.is_real one_float_i);
  check (float 0.0001) "get real (i)" 1.0 (Term.get_real one_float_i)

(* Check boolean values construction and interpretation *)
let test_val_interp_bool () =
  let tm = TermManager.mk_tm () in
  let true1 = Term.mk_bool tm true in
  is_true "is bool" (Term.is_bool true1);
  is_true "get bool" (Term.get_bool true1);

  let true2 = Term.mk_true tm in
  is_true "is bool true" (Term.is_bool true2);
  is_true "get bool true" (Term.get_bool true2)

(* Check string values construction and interpretation *)
let test_val_interp_string () =
  let tm = TermManager.mk_tm () in
  let str = Term.mk_string tm "abc" in
  is_true "is string" (Term.is_string str);
  check string "get string" "abc" (Term.get_string str)

let test_model () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  Solver.set_option solver "produce-models" "true";
  let int_sort = Sort.mk_int_sort tm in
  let zero = Term.mk_int tm 0 in
  let one = Term.mk_int tm 1 in
  let x = Term.mk_const_s tm int_sort "x" in
  let y = Term.mk_const_s tm int_sort "y" in
  let x_eq_zero = Term.mk_term tm Kind.Equal [| x; zero |] in
  let y_gt_one = Term.mk_term tm Kind.Gt [| y; one |] in
  Solver.assert_formula solver x_eq_zero;
  Solver.assert_formula solver y_gt_one;
  ignore (Solver.check_sat solver);
  (* check if model matches expected solution *)
  let sol = [| (x, 0); (y, 2) |] in
  Array.iter
    (fun (t, v) ->
      let v' = Solver.get_value solver t in
      let i = Term.get_int v' in
      check int "model value" v i )
    sol

let test_function_sort () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let int_sort = Sort.mk_int_sort tm in
  let fun_sort = Sort.mk_function_sort tm [| int_sort |] int_sort in
  let f = Term.mk_const_s tm fun_sort "f" in
  let x = Term.mk_const_s tm int_sort "x" in
  let app = Term.mk_term tm Kind.Apply_uf [| f; x |] in
  let zero = Term.mk_int tm 0 in
  let constraint_t = Term.mk_term tm Kind.Gt [| app; zero |] in
  Solver.assert_formula solver constraint_t;
  let result = Solver.check_sat solver in
  is_true "function sort is sat" (Result.is_sat result)

(* Reset the assertions of a solver and checking its satisfiability should produce SAT *)
let test_reset () =
  let tm = TermManager.mk_tm () in
  let solver = Solver.mk_solver tm in
  let false_const = Term.mk_false tm in
  Solver.assert_formula solver false_const;
  Solver.reset solver;
  let result = Solver.check_sat solver in
  is_true "reset solver is sat" (Result.is_sat result)

let () =
  Alcotest.run "cvc5"
    [ ("trivial", [ test_case "trivial sat" `Quick test_trivial ])
    ; ( "terms"
      , [ test_case "simplification" `Quick test_terms_simplification
        ; test_case "not equal" `Quick test_terms_not_equal
        ; test_case "kind" `Quick test_terms_kind
        ; test_case "check sat assuming" `Quick test_terms_check_sat_assuming
        ] )
    ; ( "val_interp"
      , [ test_case "int" `Quick test_val_interp_int
        ; test_case "real" `Quick test_val_interp_real
        ; test_case "bool" `Quick test_val_interp_bool
        ; test_case "string" `Quick test_val_interp_string
        ] )
    ; ("model", [ test_case "model generation" `Quick test_model ])
    ; ( "function_sort"
      , [ test_case "function sort and apply_uf" `Quick test_function_sort ] )
    ; ("reset", [ test_case "solver reset" `Quick test_reset ])
    ]
