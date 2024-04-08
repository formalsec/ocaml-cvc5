exception Error of string

let _ = Callback.register_exception "cvc5Exception" (Error "")

module Kind = Cvc5_enums.Kind
module RoundingMode = Cvc5_enums.RoundingMode

module TermManager = struct
  type tm = Cvc5_external.term_manager

  let mk_tm = Cvc5_external.new_term_manager

  let delete_tm = Cvc5_external.delete_term_manager
end

module Sort = struct
  type sort = Cvc5_external.sort

  let equal = Cvc5_external.sort_equal

  let to_string = Cvc5_external.sort_to_string

  let mk_bool_sort = Cvc5_external.get_boolean_sort

  let mk_int_sort = Cvc5_external.get_integer_sort

  let mk_real_sort = Cvc5_external.get_real_sort

  let mk_string_sort = Cvc5_external.get_string_sort

  let mk_bv_sort = Cvc5_external.mk_bitvector_sort

  let bv_size = Cvc5_external.sort_get_bv_size

  let mk_rm_sort = Cvc5_external.get_rm_sort

  let mk_fp_sort = Cvc5_external.mk_fp_sort

  let mk_seq_sort = Cvc5_external.mk_seq_sort

  let mk_uninterpreted_sort = Cvc5_external.mk_uninterpreted_sort
end

module Term = struct
  type term = Cvc5_external.term

  let id = Cvc5_external.term_id

  let equal = Cvc5_external.term_equal

  let kind t = Kind.of_cpp @@ Cvc5_external.term_kind t

  let sort = Cvc5_external.term_sort

  let to_string = Cvc5_external.term_to_string

  let mk_const = Cvc5_external.mk_const

  let mk_const_s = Cvc5_external.mk_const_s

  let mk_term (tm : TermManager.tm) (k : Kind.t) (terms : term array) =
    Cvc5_external.mk_term tm (Kind.to_cpp k) terms

  let mk_true = Cvc5_external.mk_true

  let mk_false = Cvc5_external.mk_false

  let mk_bool = Cvc5_external.mk_bool

  let mk_int = Cvc5_external.mk_int

  let mk_real_s = Cvc5_external.mk_real_s

  let mk_real_i = Cvc5_external.mk_real_i

  let mk_real = Cvc5_external.mk_real

  let mk_bv = Cvc5_external.mk_bv

  let mk_bv_s = Cvc5_external.mk_bv_s

  let mk_rm (tm : TermManager.tm) (rm : RoundingMode.t) =
    Cvc5_external.mk_roundingmode tm (RoundingMode.to_cpp rm)

  let is_int = Cvc5_external.term_is_int_val

  let is_real = Cvc5_external.term_is_real_val

  let is_string = Cvc5_external.term_is_string_val

  let is_bv = Cvc5_external.term_is_bv_val

  let is_int32 = Cvc5_external.term_is_int32_val

  let is_int64 = Cvc5_external.term_is_int64_val

  let is_uint32 = Cvc5_external.term_is_uint32_val

  let is_uint64 = Cvc5_external.term_is_uint64_val

  let is_rm = Cvc5_external.term_is_rm_val

  let is_bool = Cvc5_external.term_is_bool_val

  let get_int t = int_of_string (Cvc5_external.term_get_int_val t)

  let get_real t = float_of_string (Cvc5_external.term_get_real_val t)

  let get_int32 = Cvc5_external.term_get_int32_val

  let get_int64 = Cvc5_external.term_get_int64_val

  let get_bv = Cvc5_external.term_get_bv_val

  let get_uint32 = Cvc5_external.term_get_uint32_val

  let get_uint64 = Cvc5_external.term_get_uint64_val

  let get_rm t = RoundingMode.of_cpp @@ Cvc5_external.term_get_rm_val t

  let get_bool = Cvc5_external.term_get_bool_val
end

module Result = struct
  type result = Cvc5_external.result

  let equal = Cvc5_external.result_equal

  let to_string = Cvc5_external.result_to_string

  let is_sat = Cvc5_external.result_is_sat

  let is_unsat = Cvc5_external.result_is_unsat

  let is_unknown = Cvc5_external.result_is_unknown
end

module Solver = struct
  type solver = Cvc5_external.solver

  let mk_solver = Cvc5_external.new_solver

  let delete_solver = Cvc5_external.delete

  let assert_formula = Cvc5_external.assert_formula

  let check_sat = Cvc5_external.check_sat

  let set_logic = Cvc5_external.set_logic

  let set_option = Cvc5_external.set_option

  let simplify = Cvc5_external.simplify

  let push = Cvc5_external.push

  let pop = Cvc5_external.pop

  let reset = Cvc5_external.reset_assertions
end
