(* This file is automatically generated *)

(** External declarations for cvc5's Oocaml_cvc5 bindings. *)

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

external result_is_sat : ptr -> term_manager -> bool = "ocaml_cvc5_stub_result_is_sat"
external result_is_unsat : ptr -> bool = "ocaml_cvc5_stub_result_is_unsat"
external result_is_unknown : ptr -> bool = "ocaml_cvc5_stub_result_is_unknown"
external mk_true : term_manager -> term = "ocaml_cvc5_stub_mk_true"
external mk_false : term_manager -> term = "ocaml_cvc5_stub_mk_false"
external mk_bool : term_manager -> bool -> term = "ocaml_cvc5_stub_mk_bool"
external mk_int : term_manager -> int -> term = "ocaml_cvc5_stub_mk_int"
external mk_real : term_manager -> string -> term = "ocaml_cvc5_stub_mk_real"
external mk_string : term_manager -> string -> term = "ocaml_cvc5_stub_mk_string"
external mk_term : term_manager -> int -> term array -> term = "ocaml_cvc5_stub_mk_term"
external get_boolean_sort : term_manager -> sort = "ocaml_cvc5_stub_get_boolean_sort"
external get_integer_sort : term_manager -> sort = "ocaml_cvc5_stub_get_integer_sort"
external mk_const : term_manager -> sort -> string -> term = "ocaml_cvc5_stub_mk_const"
external term_to_string : term -> string = "ocaml_cvc5_stub_term_to_string"
external new_solver : term_manager -> solver = "ocaml_cvc5_stub_new_solver"
external new_term_manager : unit -> term_manager = "ocaml_cvc5_stub_new_term_manager"
external delete_term_manager : term_manager -> unit = "ocaml_cvc5_stub_delete_term_manager"
external delete : solver -> unit = "ocaml_cvc5_stub_delete"
external assert_formula : solver -> term -> unit = "ocaml_cvc5_stub_assert_formula"
external check_sat : solver -> result = "ocaml_cvc5_stub_check_sat"

(**/**)