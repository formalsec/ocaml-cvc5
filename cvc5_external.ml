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

external result_is_sat : result -> bool = "ocaml_cvc5_stub_result_is_sat"

external result_is_unsat : result -> bool = "ocaml_cvc5_stub_result_is_unsat"

external result_is_unknown : result -> bool
  = "ocaml_cvc5_stub_result_is_unknown"

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

external delete : solver -> unit = "ocaml_cvc5_stub_delete"

external assert_formula : solver -> term -> unit
  = "ocaml_cvc5_stub_assert_formula"

external check_sat : solver -> result = "ocaml_cvc5_stub_check_sat"

external check_sat_assuming : solver -> term array -> result
  = "ocaml_cvc5_stub_check_sat_assuming"

external set_logic : solver -> string -> unit = "ocaml_cvc5_stub_set_logic"

external set_option : solver -> string -> string -> unit
  = "ocaml_cvc5_stub_set_option"

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

external mk_term_1 : term_manager -> int -> term -> term
  = "ocaml_cvc5_stub_mk_term_1"

external mk_term_2 : term_manager -> int -> term -> term -> term
  = "ocaml_cvc5_stub_mk_term_2"

external mk_term_3 : term_manager -> int -> term -> term -> term -> term
  = "ocaml_cvc5_stub_mk_term_3"

(**/**)
