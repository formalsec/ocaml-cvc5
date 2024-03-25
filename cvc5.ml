exception Error of string

let _ = Callback.register_exception "cvc5Exception" (Error "")

module Kind = Kind

module TermManager =
struct
  type tm = Cvc5_external.term_manager

  let mk_tm = Cvc5_external.new_term_manager
  let delete_tm = Cvc5_external.delete_term_manager
end

module Sort =
struct
  type sort = Cvc5_external.sort

  let mk_bool_sort = Cvc5_external.get_boolean_sort
  let mk_int_sort = Cvc5_external.get_integer_sort
  let mk_real_sort = Cvc5_external.get_real_sort 
  let mk_string_sort = Cvc5_external.get_string_sort 
  let mk_bv_sort = Cvc5_external.mk_bitvector_sort
end

module Term =
struct
  type term = Cvc5_external.term

  let to_string = Cvc5_external.term_to_string
  let mk_const = Cvc5_external.mk_const
  let mk_const_s = Cvc5_external.mk_const_s
  let mk_term (tm : TermManager.tm) (k : Kind.t) (terms : term array) =
    Cvc5_external.mk_term tm (Kind.to_cpp k) terms
  let mk_true = Cvc5_external.mk_true
  let mk_false = Cvc5_external.mk_false
  let mk_bool = Cvc5_external.mk_bool
  let mk_int = Cvc5_external.mk_int
end

module Result =
struct
  type result = Cvc5_external.result

  let is_sat = Cvc5_external.result_is_sat
  let is_unsat = Cvc5_external.result_is_unsat
  let is_unknown = Cvc5_external.result_is_unknown
end

module Solver =
struct
  type solver = Cvc5_external.solver

  let mk_solver = Cvc5_external.new_solver
  let delete_solver = Cvc5_external.delete
  let assert_formula = Cvc5_external.assert_formula
  let check_sat = Cvc5_external.check_sat
  let set_logic = Cvc5_external.set_logic
  let simplify = Cvc5_external.simplify
  let push = Cvc5_external.push
  let pop = Cvc5_external.pop
  let reset = Cvc5_external.reset_assertions
end

