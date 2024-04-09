(** External declarations for cvc5's OCaml bindings. *)

(**/**)

type ptr

and result = ptr

and synth_result = ptr

and sort = ptr

and term = ptr

and op = ptr

and datatype = ptr

and datatype_constructor_decl = ptr

and datatype_decl = ptr

and datatype_selector = ptr

and datatype_constructor = ptr

and grammar = ptr

and solver = ptr

and term_manager = ptr

and option_info = ptr

and proof = ptr

and proof_rule = ptr

and statistics = ptr

and unknown_explanation = ptr

and sort_kind = ptr

and kind = ptr

and rounding_mode = ptr

and proof_format = ptr

and proof_component = ptr

and learned_lit_type = ptr

and block_model_mode = ptr

and find_synth_target = ptr

external result_is_sat : result -> bool = "ocaml_cvc5_stub_result_is_sat"
[@@noalloc]

external result_is_unsat : result -> bool = "ocaml_cvc5_stub_result_is_unsat"
[@@noalloc]

external result_is_unknown : result -> bool
  = "ocaml_cvc5_stub_result_is_unknown"
[@@noalloc]

external result_equal : result -> result -> bool
  = "ocaml_cvc5_stub_result_equal"
[@@noalloc]

external result_to_string : result -> string
  = "ocaml_cvc5_stub_result_to_string"
[@@noalloc]

external mk_true : term_manager -> term = "ocaml_cvc5_stub_mk_true"

external mk_false : term_manager -> term = "ocaml_cvc5_stub_mk_false"

external mk_bool : term_manager -> bool -> term = "ocaml_cvc5_stub_mk_bool"

external mk_int : term_manager -> int -> term = "ocaml_cvc5_stub_mk_int"

external mk_real_s : term_manager -> string -> term
  = "ocaml_cvc5_stub_mk_real_s"

external mk_real_i : term_manager -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_real_i" "native_cvc5_stub_mk_real_i"

external mk_real : term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_real" "native_cvc5_stub_mk_real"

external mk_bv : term_manager -> (int[@untagged]) -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_bv" "native_cvc5_stub_mk_bv"

external mk_bv_s :
  term_manager -> (int[@untagged]) -> string -> (int[@untagged]) -> term
  = "ocaml_cvc5_stub_mk_bv_s" "native_cvc5_stub_mk_bv_s"

external mk_string : term_manager -> string -> bool -> term
  = "ocaml_cvc5_stub_mk_string"

external mk_term : term_manager -> int -> term array -> term
  = "ocaml_cvc5_stub_mk_term"

external term_get_int_val : term -> string = "ocaml_cvc5_stub_get_int_value"

external term_is_int_val : term -> bool = "ocaml_cvc5_stub_is_int_value"
[@@noalloc]

external term_get_real_val : term -> string = "ocaml_cvc5_stub_get_real_value"

external term_is_real_val : term -> bool = "ocaml_cvc5_stub_is_real_value"
[@@noalloc]

external term_is_string_val : term -> bool = "ocaml_cvc5_stub_is_string_value"
[@@noalloc]

external term_is_int32_val : term -> bool = "ocaml_cvc5_stub_is_int32_value"
[@@noalloc]

external term_get_int32_val : term -> int32 = "ocaml_cvc5_stub_get_int32_value"
[@@noalloc]

external term_is_uint32_val : term -> bool = "ocaml_cvc5_stub_is_uint32_value"
[@@noalloc]

external term_get_uint32_val : term -> int32
  = "ocaml_cvc5_stub_get_uint32_value"
[@@noalloc]

external term_is_int64_val : term -> bool = "ocaml_cvc5_stub_is_int64_value"
[@@noalloc]

external term_get_int64_val : term -> int64 = "ocaml_cvc5_stub_get_int64_value"
[@@noalloc]

external term_is_uint64_val : term -> bool = "ocaml_cvc5_stub_is_uint64_value"
[@@noalloc]

external term_get_uint64_val : term -> int64
  = "ocaml_cvc5_stub_get_uint64_value"
[@@noalloc]

external term_is_bv_val : term -> bool = "ocaml_cvc5_stub_is_bv_value"
[@@noalloc]

external term_get_bv_val : term -> int32 -> string
  = "ocaml_cvc5_stub_get_bv_value"

external term_is_rm_val : term -> bool = "ocaml_cvc5_stub_is_rm_value"
[@@noalloc]

external term_get_rm_val : term -> int = "ocaml_cvc5_stub_get_rm_value"
[@@noalloc]

external term_is_bool_val : term -> bool = "ocaml_cvc5_stub_is_bool_value"
[@@noalloc]

external term_get_bool_val : term -> bool = "ocaml_cvc5_stub_get_bool_value"
[@@noalloc]

external get_boolean_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_boolean_sort"

external get_integer_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_integer_sort"

external get_real_sort : term_manager -> sort = "ocaml_cvc5_stub_get_real_sort"

external get_string_sort : term_manager -> sort
  = "ocaml_cvc5_stub_get_string_sort"

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
[@@noalloc]

external sort_to_string : sort -> string = "ocaml_cvc5_stub_sort_to_string"
[@@noalloc]

external sort_equal : sort -> sort -> bool = "ocaml_cvc5_stub_sort_equal"
[@@noalloc]

external mk_const_s : term_manager -> sort -> string -> term
  = "ocaml_cvc5_stub_mk_const_s"

external mk_const : term_manager -> sort -> term = "ocaml_cvc5_stub_mk_const"

external mk_roundingmode : term_manager -> int -> term
  = "ocaml_cvc5_stub_mk_rounding_mode"

external term_to_string : term -> string = "ocaml_cvc5_stub_term_to_string"

external term_equal : term -> term -> bool = "ocaml_cvc5_stub_term_equal"
[@@noalloc]

external term_id : term -> int = "ocaml_cvc5_stub_term_id" [@@noalloc]

external term_kind : term -> int = "ocaml_cvc5_stub_term_kind" [@@noalloc]

external term_sort : term -> sort = "ocaml_cvc5_stub_term_sort"

external new_solver : term_manager -> solver = "ocaml_cvc5_stub_new_solver"

external new_term_manager : unit -> term_manager
  = "ocaml_cvc5_stub_new_term_manager"

external delete_term_manager : term_manager -> unit
  = "ocaml_cvc5_stub_delete_term_manager"

external delete : solver -> unit = "ocaml_cvc5_stub_delete"

external assert_formula : solver -> term -> unit
  = "ocaml_cvc5_stub_assert_formula"
[@@noalloc]

external check_sat : solver -> result = "ocaml_cvc5_stub_check_sat"

external check_sat_assuming : solver -> term array -> result
  = "ocaml_cvc5_stub_check_sat_assuming"

external set_logic : solver -> string -> unit = "ocaml_cvc5_stub_set_logic"
[@@noalloc]

external set_option : solver -> string -> string -> unit
  = "ocaml_cvc5_stub_set_option"
[@@noalloc]

external simplify : solver -> term -> term = "ocaml_cvc5_stub_simplify"

external push : solver -> int -> unit = "ocaml_cvc5_stub_push" [@@noalloc]

external pop : solver -> int -> unit = "ocaml_cvc5_stub_pop" [@@noalloc]

external reset_assertions : solver -> unit = "ocaml_cvc5_stub_reset_assertions"
[@@noalloc]

(**/**)
