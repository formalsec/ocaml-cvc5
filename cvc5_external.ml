(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

(** External declarations for cvc5's OCaml bindings. *)

(**/**)

type ptr

type result = ptr

type synth_result = ptr

type sort = ptr

type term = ptr

type op = ptr

type datatype = ptr

type datatype_constructor_decl = ptr

type datatype_decl = ptr

type datatype_selector = ptr

type datatype_constructor = ptr

type grammar = ptr

type solver = ptr

type term_manager = ptr

type option_info = ptr

type proof = ptr

type proof_rule = ptr

type stat = ptr

type statistics = ptr

type unknown_explanation = ptr

type sort_kind = ptr

type kind = ptr

type rounding_mode = ptr

type proof_format = ptr

type proof_component = ptr

type learned_lit_type = ptr

type block_model_mode = ptr

type find_synth_target = ptr

type synthresult = ptr

external result_is_sat : result -> bool = "ocaml_cvc5_stub_result_is_sat"

external result_is_unsat : result -> bool = "ocaml_cvc5_stub_result_is_unsat"

external result_is_unknown : result -> bool
  = "ocaml_cvc5_stub_result_is_unknown"

external result_is_null : result -> bool = "ocaml_cvc5_stub_result_is_null"

external result_get_unknown_explanation : result -> int
  = "ocaml_cvc5_stub_result_get_unknown_explanation"

external result_equal : result -> result -> bool
  = "ocaml_cvc5_stub_result_equal"

external result_to_string : result -> string
  = "ocaml_cvc5_stub_result_to_string"

external mk_true : term_manager -> term = "ocaml_cvc5_stub_mk_true"

external mk_false : term_manager -> term = "ocaml_cvc5_stub_mk_false"

external mk_bool : term_manager -> bool -> term = "ocaml_cvc5_stub_mk_bool"

external mk_int : term_manager -> int -> term = "ocaml_cvc5_stub_mk_int"

external mk_real_s : term_manager -> string -> term
  = "ocaml_cvc5_stub_mk_real_s"

external mk_real_i : term_manager -> (int64[@unboxed]) -> term
  = "ocaml_cvc5_stub_mk_real_i" "native_cvc5_stub_mk_real_i"

external mk_real :
  term_manager -> (int64[@unboxed]) -> (int64[@unboxed]) -> term
  = "ocaml_cvc5_stub_mk_real" "native_cvc5_stub_mk_real"

external mk_bv : term_manager -> (int[@untagged]) -> (int64[@unboxed]) -> term
  = "ocaml_cvc5_stub_mk_bv" "native_cvc5_stub_mk_bv"

external mk_bv_s :
  term_manager -> (int[@untagged]) -> string -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_bv_s" "native_cvc5_stub_mk_bv_s"

external mk_string : term_manager -> string -> bool -> term
  = "ocaml_cvc5_stub_mk_string"

external mk_fp :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term -> term
  = "ocaml_cvc5_stub_mk_fp" "native_cvc5_stub_mk_fp"

external mk_fp_terms : term_manager -> term -> term -> term -> term
  = "ocaml_cvc5_stub_mk_fp_from_terms"

external mk_fp_pos_inf :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_fp_pos_inf" "native_cvc5_stub_mk_fp_pos_inf"

external mk_fp_neg_inf :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_fp_neg_inf" "native_cvc5_stub_mk_fp_neg_inf"

external mk_fp_nan :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_fp_nan" "native_cvc5_stub_mk_fp_nan"

external mk_fp_pos_zero :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_fp_pos_zero" "native_cvc5_stub_mk_fp_pos_zero"

external mk_fp_neg_zero :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_fp_neg_zero" "native_cvc5_stub_mk_fp_neg_zero"

external mk_term : term_manager -> int -> term array -> term
  = "ocaml_cvc5_stub_mk_term"

external mk_term_op : term_manager -> op -> term array -> term
  = "ocaml_cvc5_stub_mk_term_with_op"

external term_get_int_val : term -> string = "ocaml_cvc5_stub_get_int_value"

external term_is_int_val : term -> bool = "ocaml_cvc5_stub_is_int_value"

external term_get_real_val : term -> string = "ocaml_cvc5_stub_get_real_value"

external term_is_real_val : term -> bool = "ocaml_cvc5_stub_is_real_value"

external term_get_string_val : term -> string
  = "ocaml_cvc5_stub_get_string_value"

external term_is_string_val : term -> bool = "ocaml_cvc5_stub_is_string_value"

external term_is_int32_val : term -> bool = "ocaml_cvc5_stub_is_int32_value"

external term_get_int32_val : term -> int32 = "ocaml_cvc5_stub_get_int32_value"

external term_is_uint32_val : term -> bool = "ocaml_cvc5_stub_is_uint32_value"

external term_get_uint32_val : term -> int = "ocaml_cvc5_stub_get_uint32_value"

external term_is_int64_val : term -> bool = "ocaml_cvc5_stub_is_int64_value"

external term_get_int64_val : term -> int64 = "ocaml_cvc5_stub_get_int64_value"

external term_is_uint64_val : term -> bool = "ocaml_cvc5_stub_is_uint64_value"

external term_get_uint64_val : term -> int = "ocaml_cvc5_stub_get_uint64_value"

external term_is_bv_val : term -> bool = "ocaml_cvc5_stub_is_bv_value"

external term_get_bv_val : term -> (int[@untagged]) -> string
  = "ocaml_cvc5_stub_get_bv_value" "native_cvc5_stub_get_bv_value"

external term_is_rm_val : term -> bool = "ocaml_cvc5_stub_is_rm_value"

external term_get_rm_val : term -> int = "ocaml_cvc5_stub_get_rm_value"

external term_is_fp_val : term -> bool = "ocaml_cvc5_stub_is_fp_value"

external term_get_fp_val : term -> int * int * term
  = "ocaml_cvc5_stub_get_fp_value"

external term_is_bool_val : term -> bool = "ocaml_cvc5_stub_is_bool_value"

external term_get_bool_val : term -> bool = "ocaml_cvc5_stub_get_bool_value"

external get_boolean_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_boolean_sort"

external get_integer_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_integer_sort"

external get_real_sort : term_manager -> sort = "ocaml_cvc5_stub_get_real_sort"

external get_string_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_string_sort"

external get_regexp_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_regexp_sort"

external mk_bitvector_sort : term_manager -> int -> sort
  = "ocaml_cvc5_stub_mk_bitvector_sort"

external get_rm_sort : term_manager -> sort = "ocaml_cvc5_stub_get_rm_sort"

external mk_fp_sort :
  term_manager -> (int[@untagged]) -> (int[@untagged]) -> sort
  = "ocaml_cvc5_stub_mk_fp_sort" "native_cvc5_stub_mk_fp_sort"

external mk_seq_sort : term_manager -> sort -> sort
  = "ocaml_cvc5_stub_mk_seq_sort"

external mk_uninterpreted_sort : term_manager -> string -> sort
  = "ocaml_cvc5_stub_mk_uninterpreted_sort"

external sort_get_bv_size : sort -> int32 = "ocaml_cvc5_stub_sort_get_bv_size"

external sort_to_string : sort -> string = "ocaml_cvc5_stub_sort_to_string"

external sort_equal : sort -> sort -> bool = "ocaml_cvc5_stub_sort_equal"

external mk_const_s : term_manager -> sort -> string -> term
  = "ocaml_cvc5_stub_mk_const_s"

external mk_const : term_manager -> sort -> term = "ocaml_cvc5_stub_mk_const"

external mk_roundingmode : term_manager -> int -> rounding_mode
  = "ocaml_cvc5_stub_mk_rounding_mode"

external term_to_string : term -> string = "ocaml_cvc5_stub_term_to_string"

external term_equal : term -> term -> bool = "ocaml_cvc5_stub_term_equal"

external term_id : term -> int = "ocaml_cvc5_stub_term_id"

external term_kind : term -> int = "ocaml_cvc5_stub_term_kind"

external term_sort : term -> sort = "ocaml_cvc5_stub_term_sort"

external new_solver : term_manager -> solver = "ocaml_cvc5_stub_new_solver"

external new_term_manager : unit -> term_manager
  = "ocaml_cvc5_stub_new_term_manager"

external delete_term_manager : term_manager -> unit
  = "ocaml_cvc5_stub_delete_term_manager"

external tm_get_statistics : term_manager -> statistics
  = "ocaml_cvc5_stub_tm_get_statistics"

external tm_mk_param_sort : term_manager -> string option -> sort
  = "ocaml_cvc5_stub_mk_param_sort"

external tm_mk_unresolved_datatype_sort : term_manager -> string -> int -> sort
  = "ocaml_cvc5_stub_mk_unresolved_datatype_sort"

external tm_mk_datatype_constructor_decl :
  term_manager -> string -> datatype_constructor_decl
  = "ocaml_cvc5_stub_mk_datatype_constructor_decl"

external tm_mk_datatype_decl : term_manager -> string -> bool -> datatype_decl
  = "ocaml_cvc5_stub_mk_datatype_decl"

external tm_mk_datatype_decl_with_params :
  term_manager -> string -> sort array -> bool -> datatype_decl
  = "ocaml_cvc5_stub_mk_datatype_decl_with_params"

external delete : solver -> unit = "ocaml_cvc5_stub_delete"

external assert_formula : solver -> term -> unit
  = "ocaml_cvc5_stub_assert_formula"

external check_sat : solver -> result = "ocaml_cvc5_stub_check_sat"

external check_sat_assuming : solver -> term array -> result
  = "ocaml_cvc5_stub_check_sat_assuming"

external set_logic : solver -> string -> unit = "ocaml_cvc5_stub_set_logic"

external set_option : solver -> string -> string -> unit
  = "ocaml_cvc5_stub_set_option"

external set_info : solver -> string -> string -> unit
  = "ocaml_cvc5_stub_set_info"

external solver_is_logic_set : solver -> bool
  = "ocaml_cvc5_stub_is_logic_set"

external solver_get_logic : solver -> string = "ocaml_cvc5_stub_get_logic"

external simplify : solver -> term -> term = "ocaml_cvc5_stub_simplify"

external push : solver -> int -> unit = "ocaml_cvc5_stub_push"

external pop : solver -> int -> unit = "ocaml_cvc5_stub_pop"

external reset_assertions : solver -> unit = "ocaml_cvc5_stub_reset_assertions"

external delete_term : term -> unit = "ocaml_cvc5_stub_delete_term"

external delete_sort : sort -> unit = "ocaml_cvc5_stub_delete_sort"

external delete_result : result -> unit = "ocaml_cvc5_stub_delete_result"

external solver_get_value : solver -> term -> term
  = "ocaml_cvc5_stub_solver_get_value"

external solver_get_values : solver -> term array -> term array
  = "ocaml_cvc5_stub_solver_get_values"

external solver_get_model_domain_elements : solver -> sort -> term array
  = "ocaml_cvc5_stub_get_model_domain_elements"

external solver_get_unsat_core : solver -> term array
  = "ocaml_cvc5_stub_get_unsat_core"

external solver_get_assertions : solver -> term array
  = "ocaml_cvc5_stub_get_assertions"

external solver_get_info : solver -> string -> string
  = "ocaml_cvc5_stub_get_info"

external solver_get_option : solver -> string -> string
  = "ocaml_cvc5_stub_get_option"

external solver_get_option_names : solver -> string array
  = "ocaml_cvc5_stub_get_option_names"

external solver_get_option_info : solver -> string -> option_info
  = "ocaml_cvc5_stub_get_option_info"

external solver_get_unsat_assumptions : solver -> term array
  = "ocaml_cvc5_stub_get_unsat_assumptions"

external solver_get_unsat_core_lemmas : solver -> term array
  = "ocaml_cvc5_stub_get_unsat_core_lemmas"

external solver_get_difficulty : solver -> (term * term) array
  = "ocaml_cvc5_stub_get_difficulty"

external solver_get_timeout_core : solver -> result * term array
  = "ocaml_cvc5_stub_get_timeout_core"

external solver_get_timeout_core_assuming : solver -> term array -> result * term array
  = "ocaml_cvc5_stub_get_timeout_core_assuming"

external solver_get_proof : solver -> int -> proof array
  = "ocaml_cvc5_stub_get_proof"

external solver_proof_to_string : solver -> proof -> int -> string
  = "ocaml_cvc5_stub_proof_to_string"

external solver_get_learned_literals : solver -> int -> term array
  = "ocaml_cvc5_stub_get_learned_literals"

external solver_get_quantifier_elimination : solver -> term -> term
  = "ocaml_cvc5_stub_get_quantifier_elimination"

external solver_get_quantifier_elimination_disjunct : solver -> term -> term
  = "ocaml_cvc5_stub_get_quantifier_elimination_disjunct"

external solver_declare_sep_heap : solver -> sort -> sort -> unit
  = "ocaml_cvc5_stub_declare_sep_heap"

external solver_get_value_sep_heap : solver -> term
  = "ocaml_cvc5_stub_get_value_sep_heap"

external solver_get_value_sep_nil : solver -> term
  = "ocaml_cvc5_stub_get_value_sep_nil"

external solver_declare_pool : solver -> string -> sort -> term array -> term
  = "ocaml_cvc5_stub_declare_pool"

external solver_block_model : solver -> int -> unit
  = "ocaml_cvc5_stub_block_model"

external solver_block_model_values : solver -> term array -> unit
  = "ocaml_cvc5_stub_block_model_values"

external solver_get_instantiations : solver -> string
  = "ocaml_cvc5_stub_get_instantiations"

external solver_get_interpolant : solver -> term -> term
  = "ocaml_cvc5_stub_get_interpolant"

external solver_get_interpolant_grammar : solver -> term -> grammar -> term
  = "ocaml_cvc5_stub_get_interpolant_grammar"

external solver_get_interpolant_next : solver -> term
  = "ocaml_cvc5_stub_get_interpolant_next"

external solver_get_abduct : solver -> term -> term
  = "ocaml_cvc5_stub_get_abduct"

external solver_get_abduct_grammar : solver -> term -> grammar -> term
  = "ocaml_cvc5_stub_get_abduct_grammar"

external solver_get_abduct_next : solver -> term
  = "ocaml_cvc5_stub_get_abduct_next"

external solver_get_statistics : solver -> statistics
  = "ocaml_cvc5_stub_solver_get_statistics"

external solver_get_model : solver -> sort array -> term array -> string
  = "ocaml_cvc5_stub_get_model"

external mk_op : term_manager -> int -> int array -> op
  = "ocaml_cvc5_stub_mk_op"

external op_to_string : op -> string = "ocaml_cvc5_stub_op_to_string"

external op_equal : op -> op -> bool = "ocaml_cvc5_stub_op_equal"

external op_get_kind : op -> int = "ocaml_cvc5_stub_op_get_kind"

external op_get_num_indices : op -> int = "ocaml_cvc5_stub_op_get_num_indices"

external op_get_index : op -> int -> term = "ocaml_cvc5_stub_op_get_index"

external op_is_indexed : op -> bool = "ocaml_cvc5_stub_op_is_indexed"

external op_hash : op -> (int[@untagged])
  = "ocaml_cvc5_stub_op_hash" "native_cvc5_stub_op_hash"

external op_delete : op -> unit = "ocaml_cvc5_stub_op_delete"

external solver_declare_fun : solver -> string -> sort array -> sort -> term
  = "ocaml_cvc5_stub_declare_fun"

external mk_var_s : term_manager -> sort -> string -> term
  = "ocaml_cvc5_stub_mk_var_s"

external mk_var : term_manager -> sort -> term = "ocaml_cvc5_stub_mk_var"

external solver_define_fun :
  solver -> string -> term array -> sort -> term -> term
  = "ocaml_cvc5_stub_define_fun"

external solver_define_fun_rec :
  solver -> string -> term array -> sort -> term -> bool -> term
  = "ocaml_cvc5_stub_define_fun_rec_bytecode"
    "ocaml_cvc5_stub_define_fun_rec"

external solver_define_fun_rec_term :
  solver -> term -> term array -> term -> bool -> term
  = "ocaml_cvc5_stub_define_fun_rec_term"

external solver_define_funs_rec :
  solver -> term array -> term array array -> term array -> bool -> unit
  = "ocaml_cvc5_stub_define_funs_rec"

external solver_declare_sort : solver -> string -> int -> bool -> sort
  = "ocaml_cvc5_stub_declare_sort"

external solver_declare_datatype :
  solver -> string -> datatype_constructor_decl array -> sort
  = "ocaml_cvc5_stub_declare_datatype"

external mk_term_1 : term_manager -> int -> term -> term
  = "ocaml_cvc5_stub_mk_term_1"

external mk_term_2 : term_manager -> int -> term -> term -> term
  = "ocaml_cvc5_stub_mk_term_2"

external mk_term_3 : term_manager -> int -> term -> term -> term -> term
  = "ocaml_cvc5_stub_mk_term_3"

external solver_mk_grammar : solver -> term array -> term array -> grammar
  = "ocaml_cvc5_stub_solver_mk_grammar"

external solver_synth_fun_with_grammar :
  solver -> term_manager -> string -> term array -> sort -> grammar -> term
  = "ocaml_cvc5_stub_synth_fun_unpack"
    "ocaml_cvc5_stub_solver_synth_fun_grammar"

external solver_synth_fun_no_grammar :
  solver -> term_manager -> string -> term array -> sort -> term
  = "ocaml_cvc5_stub_solver_synth_fun"

external solver_declare_sygus_var : solver -> string -> sort -> term
  = "ocaml_cvc5_stub_solver_declare_sygus_var"

external solver_add_sygus_constraint : solver -> term -> unit
  = "ocaml_cvc5_stub_solver_add_sygus_constraint"

external solver_get_sygus_constraints : solver -> term array
  = "ocaml_cvc5_stub_solver_get_sygus_constraints"

external solver_add_sygus_assume : solver -> term -> unit
  = "ocaml_cvc5_stub_solver_add_sygus_assume"

external solver_get_sygus_assumptions : solver -> term array
  = "ocaml_cvc5_stub_solver_get_sygus_assumptions"

external solver_add_sygus_inv_constraint :
  solver -> term -> term -> term -> term -> unit
  = "ocaml_cvc5_stub_solver_add_sygus_inv_constraint"

external solver_check_synth : solver -> synthresult
  = "ocaml_cvc5_stub_solver_check_synth"

external solver_check_synth_next : solver -> synthresult
  = "ocaml_cvc5_stub_solver_check_synth_next"

external solver_get_synth_solution : solver -> term -> term
  = "ocaml_cvc5_stub_solver_get_synth_solution"

external solver_get_synth_solutions : solver -> term array -> term array
  = "ocaml_cvc5_stub_solver_get_synth_solutions"

external solver_find_synth : solver -> int -> term
  = "ocaml_cvc5_stub_solver_find_synth"

external solver_find_synth_grammar : solver -> int -> grammar -> term
  = "ocaml_cvc5_stub_solver_find_synth_grammar"

external grammar_add_rules : grammar -> term -> term array -> unit
  = "ocaml_cvc5_stub_grammar_add_rules"

external grammar_add_rule : grammar -> term -> term -> unit
  = "ocaml_cvc5_stub_grammar_add_rule"

external grammar_add_any_constant : grammar -> term -> unit
  = "ocaml_cvc5_stub_grammar_add_any_constant"

external grammar_add_any_variable : grammar -> term -> unit
  = "ocaml_cvc5_stub_grammar_add_any_variable"

external grammar_is_null : grammar -> bool = "ocaml_cvc5_stub_grammar_is_null"

external grammar_to_string : grammar -> string
  = "ocaml_cvc5_stub_grammar_to_string"

external sort_is_null : sort -> bool = "ocaml_cvc5_stub_sort_is_null"

external sort_is_boolean : sort -> bool = "ocaml_cvc5_stub_sort_is_boolean"

external sort_is_integer : sort -> bool = "ocaml_cvc5_stub_sort_is_integer"

external sort_is_real : sort -> bool = "ocaml_cvc5_stub_sort_is_real"

external sort_is_string : sort -> bool = "ocaml_cvc5_stub_sort_is_string"

external sort_is_regexp : sort -> bool = "ocaml_cvc5_stub_sort_is_regexp"

external sort_is_rm : sort -> bool = "ocaml_cvc5_stub_sort_is_rm"

external sort_is_bv : sort -> bool = "ocaml_cvc5_stub_sort_is_bv"

external sort_is_fp : sort -> bool = "ocaml_cvc5_stub_sort_is_fp"

external sort_is_datatype : sort -> bool = "ocaml_cvc5_stub_sort_is_datatype"

external sort_is_datatype_constructor : sort -> bool
  = "ocaml_cvc5_stub_sort_is_datatype_constructor"

external sort_is_datatype_selector : sort -> bool
  = "ocaml_cvc5_stub_sort_is_datatype_selector"

external sort_is_datatype_tester : sort -> bool
  = "ocaml_cvc5_stub_sort_is_datatype_tester"

external sort_is_function : sort -> bool = "ocaml_cvc5_stub_sort_is_function"

external sort_is_predicate : sort -> bool
  = "ocaml_cvc5_stub_sort_is_predicate"

external sort_is_tuple : sort -> bool = "ocaml_cvc5_stub_sort_is_tuple"

external sort_is_nullable : sort -> bool = "ocaml_cvc5_stub_sort_is_nullable"

external sort_is_record : sort -> bool = "ocaml_cvc5_stub_sort_is_record"

external sort_is_array : sort -> bool = "ocaml_cvc5_stub_sort_is_array"

external sort_is_finite_field : sort -> bool
  = "ocaml_cvc5_stub_sort_is_finite_field"

external sort_is_set : sort -> bool = "ocaml_cvc5_stub_sort_is_set"

external sort_is_bag : sort -> bool = "ocaml_cvc5_stub_sort_is_bag"

external sort_is_sequence : sort -> bool = "ocaml_cvc5_stub_sort_is_sequence"

external sort_is_abstract : sort -> bool = "ocaml_cvc5_stub_sort_is_abstract"

external sort_is_uninterpreted_sort : sort -> bool
  = "ocaml_cvc5_stub_sort_is_uninterpreted_sort"

external sort_is_uninterpreted_sort_constructor : sort -> bool
  = "ocaml_cvc5_stub_sort_is_uninterpreted_sort_constructor"

external sort_is_instantiated : sort -> bool
  = "ocaml_cvc5_stub_sort_is_instantiated"

external sort_get_uninterpreted_sort_constructor : sort -> sort
  = "ocaml_cvc5_stub_sort_get_uninterpreted_sort_constructor"

external sort_get_datatype : sort -> datatype = "ocaml_cvc5_stub_sort_get_datatype"

external sort_instantiate : sort -> sort array -> sort
  = "ocaml_cvc5_stub_sort_instantiate"

external sort_get_instantiated_parameters : sort -> sort array
  = "ocaml_cvc5_stub_sort_get_instantiated_parameters"

external sort_substitute : sort -> sort -> sort -> sort
  = "ocaml_cvc5_stub_sort_substitute"

external sort_substitute_many : sort -> sort array -> sort array -> sort
  = "ocaml_cvc5_stub_sort_substitute_many"

external term_get_num_children : term -> int
  = "ocaml_cvc5_stub_term_get_num_children"

external term_get_child : term -> int -> term = "ocaml_cvc5_stub_term_get_child"

external term_substitute : term -> term -> term -> term
  = "ocaml_cvc5_stub_term_substitute"

external term_substitute_many : term -> term array -> term array -> term
  = "ocaml_cvc5_stub_term_substitute_many"

external term_has_op : term -> bool = "ocaml_cvc5_stub_term_has_op"

external term_get_op : term -> op = "ocaml_cvc5_stub_term_get_op"

external term_has_symbol : term -> bool = "ocaml_cvc5_stub_term_has_symbol"

external term_get_symbol : term -> string = "ocaml_cvc5_stub_term_get_symbol"

external term_is_null : term -> bool = "ocaml_cvc5_stub_term_is_null"

external term_not_term : term -> term = "ocaml_cvc5_stub_term_not_term"

external term_and_term : term -> term -> term = "ocaml_cvc5_stub_term_and_term"

external term_or_term : term -> term -> term = "ocaml_cvc5_stub_term_or_term"

external term_xor_term : term -> term -> term = "ocaml_cvc5_stub_term_xor_term"

external term_eq_term : term -> term -> term = "ocaml_cvc5_stub_term_eq_term"

external term_imp_term : term -> term -> term = "ocaml_cvc5_stub_term_imp_term"

external term_ite_term : term -> term -> term -> term
  = "ocaml_cvc5_stub_term_ite_term"

external delete_datatype_constructor_decl : datatype_constructor_decl -> unit
  = "ocaml_cvc5_stub_delete_datatype_constructor_decl"

external datatype_constructor_decl_equal :
  datatype_constructor_decl -> datatype_constructor_decl -> bool
  = "ocaml_cvc5_stub_datatype_constructor_decl_equal"

external datatype_constructor_decl_add_selector :
  datatype_constructor_decl -> string -> sort -> unit
  = "ocaml_cvc5_stub_datatype_constructor_decl_add_selector"

external datatype_constructor_decl_add_selector_self :
  datatype_constructor_decl -> string -> unit
  = "ocaml_cvc5_stub_datatype_constructor_decl_add_selector_self"

external datatype_constructor_decl_add_selector_unresolved :
  datatype_constructor_decl -> string -> string -> unit
  = "ocaml_cvc5_stub_datatype_constructor_decl_add_selector_unresolved"

external datatype_constructor_decl_is_null :
  datatype_constructor_decl -> bool
  = "ocaml_cvc5_stub_datatype_constructor_decl_is_null"

external datatype_constructor_decl_to_string :
  datatype_constructor_decl -> string
  = "ocaml_cvc5_stub_datatype_constructor_decl_to_string"

external delete_datatype_decl : datatype_decl -> unit
  = "ocaml_cvc5_stub_delete_datatype_decl"

external datatype_decl_equal : datatype_decl -> datatype_decl -> bool
  = "ocaml_cvc5_stub_datatype_decl_equal"

external datatype_decl_add_constructor :
  datatype_decl -> datatype_constructor_decl -> unit
  = "ocaml_cvc5_stub_datatype_decl_add_constructor"

external datatype_decl_get_num_constructors : datatype_decl -> int
  = "ocaml_cvc5_stub_datatype_decl_get_num_constructors"

external datatype_decl_is_parametric : datatype_decl -> bool
  = "ocaml_cvc5_stub_datatype_decl_is_parametric"

external datatype_decl_is_resolved : datatype_decl -> bool
  = "ocaml_cvc5_stub_datatype_decl_is_resolved"

external datatype_decl_is_null : datatype_decl -> bool
  = "ocaml_cvc5_stub_datatype_decl_is_null"

external datatype_decl_to_string : datatype_decl -> string
  = "ocaml_cvc5_stub_datatype_decl_to_string"

external datatype_decl_get_name : datatype_decl -> string
  = "ocaml_cvc5_stub_datatype_decl_get_name"

external delete_datatype_selector : datatype_selector -> unit
  = "ocaml_cvc5_stub_delete_datatype_selector"

external datatype_selector_equal : datatype_selector -> datatype_selector -> bool
  = "ocaml_cvc5_stub_datatype_selector_equal"

external datatype_selector_get_name : datatype_selector -> string
  = "ocaml_cvc5_stub_datatype_selector_get_name"

external datatype_selector_get_term : datatype_selector -> term
  = "ocaml_cvc5_stub_datatype_selector_get_term"

external datatype_selector_get_updater_term : datatype_selector -> term
  = "ocaml_cvc5_stub_datatype_selector_get_updater_term"

external datatype_selector_get_codomain_sort : datatype_selector -> sort
  = "ocaml_cvc5_stub_datatype_selector_get_codomain_sort"

external datatype_selector_is_null : datatype_selector -> bool
  = "ocaml_cvc5_stub_datatype_selector_is_null"

external datatype_selector_to_string : datatype_selector -> string
  = "ocaml_cvc5_stub_datatype_selector_to_string"

external delete_datatype_constructor : datatype_constructor -> unit
  = "ocaml_cvc5_stub_delete_datatype_constructor"

external datatype_constructor_equal :
  datatype_constructor -> datatype_constructor -> bool
  = "ocaml_cvc5_stub_datatype_constructor_equal"

external datatype_constructor_get_name : datatype_constructor -> string
  = "ocaml_cvc5_stub_datatype_constructor_get_name"

external datatype_constructor_get_term : datatype_constructor -> term
  = "ocaml_cvc5_stub_datatype_constructor_get_term"

external datatype_constructor_get_instantiated_term :
  datatype_constructor -> sort -> term
  = "ocaml_cvc5_stub_datatype_constructor_get_instantiated_term"

external datatype_constructor_get_tester_term : datatype_constructor -> term
  = "ocaml_cvc5_stub_datatype_constructor_get_tester_term"

external datatype_constructor_get_num_selectors : datatype_constructor -> int
  = "ocaml_cvc5_stub_datatype_constructor_get_num_selectors"

external datatype_constructor_get_selector_at :
  datatype_constructor -> int -> datatype_selector
  = "ocaml_cvc5_stub_datatype_constructor_get_selector_at"

external datatype_constructor_get_selector :
  datatype_constructor -> string -> datatype_selector
  = "ocaml_cvc5_stub_datatype_constructor_get_selector"

external datatype_constructor_is_null : datatype_constructor -> bool
  = "ocaml_cvc5_stub_datatype_constructor_is_null"

external datatype_constructor_to_string : datatype_constructor -> string
  = "ocaml_cvc5_stub_datatype_constructor_to_string"

external delete_datatype : datatype -> unit = "ocaml_cvc5_stub_delete_datatype"

external datatype_equal : datatype -> datatype -> bool
  = "ocaml_cvc5_stub_datatype_equal"

external datatype_get_constructor_at : datatype -> int -> datatype_constructor
  = "ocaml_cvc5_stub_datatype_get_constructor_at"

external datatype_get_constructor : datatype -> string -> datatype_constructor
  = "ocaml_cvc5_stub_datatype_get_constructor"

external datatype_get_selector : datatype -> string -> datatype_selector
  = "ocaml_cvc5_stub_datatype_get_selector"

external datatype_get_name : datatype -> string = "ocaml_cvc5_stub_datatype_get_name"

external datatype_get_num_constructors : datatype -> int
  = "ocaml_cvc5_stub_datatype_get_num_constructors"

external datatype_get_parameters : datatype -> sort array
  = "ocaml_cvc5_stub_datatype_get_parameters"

external datatype_is_parametric : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_parametric"

external datatype_is_codatatype : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_codatatype"

external datatype_is_tuple : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_tuple"

external datatype_is_record : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_record"

external datatype_is_finite : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_finite"

external datatype_is_well_founded : datatype -> bool
  = "ocaml_cvc5_stub_datatype_is_well_founded"

external datatype_is_null : datatype -> bool = "ocaml_cvc5_stub_datatype_is_null"

external datatype_to_string : datatype -> string
  = "ocaml_cvc5_stub_datatype_to_string"

external delete_proof : proof -> unit = "ocaml_cvc5_stub_delete_proof"

external proof_equal : proof -> proof -> bool = "ocaml_cvc5_stub_proof_equal"

external proof_is_null : proof -> bool = "ocaml_cvc5_stub_proof_is_null"

external proof_get_result : proof -> term = "ocaml_cvc5_stub_proof_get_result"

external proof_get_children : proof -> proof array
  = "ocaml_cvc5_stub_proof_get_children"

external proof_get_arguments : proof -> term array
  = "ocaml_cvc5_stub_proof_get_arguments"

external delete_option_info : option_info -> unit
  = "ocaml_cvc5_stub_delete_option_info"

external option_info_to_string : option_info -> string
  = "ocaml_cvc5_stub_option_info_to_string"

external option_info_name : option_info -> string
  = "ocaml_cvc5_stub_option_info_name"

external option_info_aliases : option_info -> string array
  = "ocaml_cvc5_stub_option_info_aliases"

external option_info_no_supports : option_info -> string array
  = "ocaml_cvc5_stub_option_info_no_supports"

external option_info_set_by_user : option_info -> bool
  = "ocaml_cvc5_stub_option_info_set_by_user"

external option_info_category : option_info -> int
  = "ocaml_cvc5_stub_option_info_category"

external option_info_is_bool : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_bool"

external option_info_is_string : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_string"

external option_info_is_int : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_int"

external option_info_is_uint : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_uint"

external option_info_is_double : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_double"

external option_info_is_mode : option_info -> bool
  = "ocaml_cvc5_stub_option_info_is_mode"

external option_info_bool_value : option_info -> bool
  = "ocaml_cvc5_stub_option_info_bool_value"

external option_info_string_value : option_info -> string
  = "ocaml_cvc5_stub_option_info_string_value"

external option_info_int_value : option_info -> int64
  = "ocaml_cvc5_stub_option_info_int_value"

external option_info_uint_value : option_info -> int64
  = "ocaml_cvc5_stub_option_info_uint_value"

external option_info_double_value : option_info -> float
  = "ocaml_cvc5_stub_option_info_double_value"

external delete_stat : stat -> unit = "ocaml_cvc5_stub_delete_stat"

external stat_to_string : stat -> string = "ocaml_cvc5_stub_stat_to_string"

external stat_is_internal : stat -> bool = "ocaml_cvc5_stub_stat_is_internal"

external stat_is_default : stat -> bool = "ocaml_cvc5_stub_stat_is_default"

external stat_is_int : stat -> bool = "ocaml_cvc5_stub_stat_is_int"

external stat_get_int : stat -> int64 = "ocaml_cvc5_stub_stat_get_int"

external stat_is_double : stat -> bool = "ocaml_cvc5_stub_stat_is_double"

external stat_get_double : stat -> float = "ocaml_cvc5_stub_stat_get_double"

external stat_is_string : stat -> bool = "ocaml_cvc5_stub_stat_is_string"

external stat_get_string : stat -> string = "ocaml_cvc5_stub_stat_get_string"

external stat_is_histogram : stat -> bool
  = "ocaml_cvc5_stub_stat_is_histogram"

external stat_get_histogram : stat -> (string * int64) array
  = "ocaml_cvc5_stub_stat_get_histogram"

external delete_statistics : statistics -> unit
  = "ocaml_cvc5_stub_delete_statistics"

external statistics_to_string : statistics -> string
  = "ocaml_cvc5_stub_statistics_to_string"

external statistics_get : statistics -> string -> stat
  = "ocaml_cvc5_stub_statistics_get"

external statistics_entries : statistics -> (string * stat) array
  = "ocaml_cvc5_stub_statistics_entries"

external synth_is_null : synthresult -> bool
  = "ocaml_cvc5_stub_synthresult_is_null"

external synth_has_solution : synthresult -> bool
  = "ocaml_cvc5_stub_synthresult_has_solution"

external synth_has_no_solution : synthresult -> bool
  = "ocaml_cvc5_stub_synthresult_no_solution"

external synth_is_unknown : synthresult -> bool
  = "ocaml_cvc5_stub_synthresult_is_unknown"

external synth_to_string : synthresult -> string
  = "ocaml_cvc5_stub_synthresult_to_string"

(**/**)
