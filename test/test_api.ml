(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let () =
  Solver.set_option solver "produce-proofs" "true";
  Solver.set_option solver "produce-unsat-assumptions" "true";
  Solver.set_option solver "incremental" "true"

let int_sort = Sort.mk_int_sort tm

let bool_sort = Sort.mk_bool_sort tm

let x = Term.mk_const_s tm int_sort "x"

let y = Term.mk_const_s tm int_sort "y"

let zero = Term.mk_int tm 0

let one = Term.mk_int tm 1

let () =
  assert (Sort.is_int int_sort);
  assert (Sort.is_bool bool_sort);
  assert (String.length (Sort.to_string (Sort.mk_param_sort tm ~name:"T" ())) > 0)

let () =
  assert (Term.has_symbol x);
  assert (Term.get_symbol x = "x");
  let sum = Term.mk_term tm Kind.Add [| x; one |] in
  assert (Term.get_num_children sum = 2);
  assert (Term.equal (Term.get_child sum 0) x);
  let sum' = Term.substitute sum x y in
  assert (String.equal (Term.to_string sum') "(+ y 1)");
  let conj = Term.and_term (Term.eq_term x zero) (Term.eq_term y one) in
  assert (Term.has_op conj);
  assert (Op.kind (Term.get_op conj) = Kind.And)

let () =
  let extract = Op.mk_op tm Kind.Bitvector_extract [| 7; 0 |] in
  assert (Op.is_indexed extract);
  assert (Op.get_num_indices extract = 2);
  assert (String.equal (Term.to_string (Op.get_index extract 0)) "7")

let () =
  let list_nil = DatatypeConstructorDecl.mk tm "nil" in
  let list_cons = DatatypeConstructorDecl.mk tm "cons" in
  DatatypeConstructorDecl.add_selector list_cons "head" int_sort;
  DatatypeConstructorDecl.add_selector_self list_cons "tail";
  let list_sort = Solver.declare_datatype solver "List" [| list_nil; list_cons |] in
  let dt = Datatype.of_sort list_sort in
  assert (Datatype.get_name dt = "List");
  assert (Datatype.get_num_constructors dt = 2);
  let cons = Datatype.get_constructor dt "cons" in
  assert (DatatypeConstructor.get_num_selectors cons = 2);
  assert
    (DatatypeSelector.get_name (DatatypeConstructor.get_selector cons "head")
    = "head")

let () =
  let pred = Term.mk_term tm Kind.Geq [| x; zero |] in
  let bx = Term.mk_var_s tm int_sort "bx" in
  ignore (Solver.define_fun_rec solver "id_rec" [| bx |] int_sort bx);
  Solver.assert_formula solver pred;
  let assertions = Solver.get_assertions solver in
  assert (Array.exists (Term.equal pred) assertions);
  assert (Solver.is_logic_set solver = false)

let () =
  let oi = Solver.get_option_info solver "produce-proofs" in
  assert (String.length (OptionInfo.to_string oi) > 0);
  assert (OptionInfo.is_bool oi);
  ignore (OptionInfo.bool_value oi)

let () =
  let stats = Solver.get_statistics solver in
  assert (String.length (Statistics.to_string stats) > 0);
  ignore (Statistics.entries stats)

let () =
  let assumption = Term.mk_term tm Kind.Lt [| x; zero |] in
  let res = Solver.check_sat_assuming solver [| assumption |] in
  assert (Result.is_unsat res);
  assert (not (Result.is_null res));
  let unsat_assumptions = Solver.get_unsat_assumptions solver in
  assert (Array.length unsat_assumptions = 1);
  let proofs = Solver.get_proof solver in
  assert (Array.length proofs > 0);
  assert (String.length (Solver.proof_to_string solver proofs.(0)) > 0)
