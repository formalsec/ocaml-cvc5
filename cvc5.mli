(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

exception Error of string

module Kind = Cvc5_enums.Kind
module RoundingMode = Cvc5_enums.RoundingMode

module TermManager : sig
  type tm

  (** TermManager instance constructor. *)
  val mk_tm : unit -> tm

  (** TermManager instance destructor. *)
  val delete : tm -> unit
end

module Sort : sig
  type sort

  (** Sort instance destructor. *)
  val delete : sort -> unit

  (** Comparison for structural equality. *)
  val equal : sort -> sort -> bool

  (** Get a string representation of the sort. *)
  val to_string : sort -> string

  (** Get the Boolean sort. *)
  val mk_bool_sort : TermManager.tm -> sort

  (** Get the Integer sort. *)
  val mk_int_sort : TermManager.tm -> sort

  (** Get the Real sort. *)
  val mk_real_sort : TermManager.tm -> sort

  (** Get the String sort. *)
  val mk_string_sort : TermManager.tm -> sort

  (** Get the RegExp sort. *)
  val mk_regexp_sort : TermManager.tm -> sort

  (** Create a bit-vector sort.

      Parameters: - The bit-width of the bit-vector sort. *)
  val mk_bv_sort : TermManager.tm -> int -> sort

  (** Get the bit-width of the bit-vector sort. *)
  val bv_size : sort -> int32

  (** Get the rounding mode sort. *)
  val mk_rm_sort : TermManager.tm -> sort

  (** Create a floating-point sort.

      Parameters: – The bit-width of the exponent of the floating-point sort.
      - The bit-width of the significand of the floating-point sort. *)
  val mk_fp_sort : TermManager.tm -> int -> int -> sort

  (** Create a sequence sort.

      Parameters: - The sort of the sequence elements. *)
  val mk_seq_sort : TermManager.tm -> sort -> sort

  (** Create an uninterpreted sort.

      Parameters: - The name of the sort. *)
  val mk_uninterpreted_sort : TermManager.tm -> string -> sort
end

module Op : sig
  type op

  (** Create operator of Kind:
      - [BITVECTOR_EXTRACT]
      - [BITVECTOR_REPEAT]
      - [BITVECTOR_ROTATE_LEFT]
      - [BITVECTOR_ROTATE_RIGHT]
      - [BITVECTOR_SIGN_EXTEND]
      - [BITVECTOR_ZERO_EXTEND]
      - [DIVISIBLE]
      - [FLOATINGPOINT_TO_FP_FROM_FP]
      - [FLOATINGPOINT_TO_FP_FROM_IEEE_BV]
      - [FLOATINGPOINT_TO_FP_FROM_REAL]
      - [FLOATINGPOINT_TO_FP_FROM_SBV]
      - [FLOATINGPOINT_TO_FP_FROM_UBV]
      - [FLOATINGPOINT_TO_SBV]
      - [FLOATINGPOINT_TO_UBV]
      - [INT_TO_BITVECTOR]
      - [TUPLE_PROJECT]

      Parameters: - The kind of the operator.
      - The arguments (indices) of the operator. *)
  val mk_op : TermManager.tm -> Kind.t -> int array -> op

  (** Syntactic equality operator. *)
  val equal : op -> op -> bool

  (** Get the string representation of the operator. *)
  val to_string : op -> string

  (** Op instance destructor *)
  val delete : op -> unit

  (** Determine if the operator is indexed. *)
  val is_indexed : op -> bool

  (* val get_index : op -> int -> Term.term *)

  (** Get the kind of the operator. *)
  val kind : op -> Kind.t

  (** Hash function for Ops. *)
  val hash : op -> int

  (** Get the number of indices of the operator. *)
  val get_num_indices : op -> int
end

module Term : sig
  type term

  (** Term instance destructor *)
  val delete : term -> unit

  (** Get the id of the term. *)
  val id : term -> int

  (** Syntactic equality operator. *)
  val equal : term -> term -> bool

  (** Get the kind of the term. *)
  val kind : term -> Kind.t

  (** Get the sort of the term. *)
  val sort : term -> Sort.sort

  (** Get the string representation of the term. *)
  val to_string : term -> string

  (** Create a free constant.

      Parameters: - The sort of the constant *)
  val mk_const : TermManager.tm -> Sort.sort -> term

  (** Create a named free constant.

      Parameters: - The sort of the constant
      - The name of the constant *)
  val mk_const_s : TermManager.tm -> Sort.sort -> string -> term

  (** Create a bound variable to be used in a binder (i.e., a quantifier, a
      lambda, or a witness binder).

      Parameters: - The sort of the variable *)
  val mk_var : TermManager.tm -> Sort.sort -> term

  (** Create a named bound variable to be used in a binder (i.e., a quantifier,
      a lambda, or a witness binder).

      Parameters: - The sort of the variable
      - The name of the variable *)
  val mk_var_s : TermManager.tm -> Sort.sort -> string -> term

  (** Create n-ary term of given kind.

      Parameters: - The kind of the term
      - The children of the term *)
  val mk_term : TermManager.tm -> Kind.t -> term array -> term

  (** Create a unary term of a given kind.

      Parameters: - The kind of the term
      - The child of the term *)
  val mk_term_1 : TermManager.tm -> Kind.t -> term -> term

  (** Create a binary term of a given kind.

      Parameters: - The kind of the term
      - The children of the term *)
  val mk_term_2 : TermManager.tm -> Kind.t -> term -> term -> term

  (** Create a ternary term of a given kind.

      Parameters: - The kind of the term
      - The children of the term *)
  val mk_term_3 : TermManager.tm -> Kind.t -> term -> term -> term -> term

  (** Create n-ary term of a given kind from a given operator.

      Parameters: - The operator
      - The children of the term *)
  val mk_term_op : TermManager.tm -> Op.op -> term array -> term

  (** Create a Boolean true constant. *)
  val mk_true : TermManager.tm -> term

  (** Create a Boolean false constant. *)
  val mk_false : TermManager.tm -> term

  (** Create a Boolean constant.

      Parameters: - The value of the constant *)
  val mk_bool : TermManager.tm -> bool -> term

  (** Create an integer constant.

      Parameters: - The value of the constant *)
  val mk_int : TermManager.tm -> int -> term

  (** Create a String constant from a string which may contain SMT-LIB
      compatible escape sequences like [\u1234] to encode unicode characters.

      Parameters: - The string this constant represents
      - (optional) A boolean that determines whether the escape sequences in the
        string should be converted to the corresponding unicode character *)
  val mk_string : TermManager.tm -> ?useEscSequences:bool -> string -> term

  (** Create a real constant from a string.

      Parameters: - The string representation of the constant, may represent an
      integer (e.g., "123") or a real constant (e.g., "12.34" or "12/34") *)
  val mk_real_s : TermManager.tm -> string -> term

  (** Create a real constant from an integer.

      Parameters: - The value of the constant *)
  val mk_real_i : TermManager.tm -> int64 -> term

  (** Create a real constant from a rational.

      Parameters: - The value of the numerator
      - The value of the denominator *)
  val mk_real : TermManager.tm -> int64 -> int64 -> term

  (** Create a bit-vector constant of a given size and value.

      Parameters: - The bit-width of the bit-vector sort
      - The value of the constant *)
  val mk_bv : TermManager.tm -> int -> int64 -> term

  (** Create a bit-vector constant of a given bit-width from a given string of
      base [2], [10], or [16].

      Parameters: - The bit-width of the constant
      - The string representation of the constant
      - The base of the string representation ([2] for binary, [10] for decimal,
        and [16] for hexadecimal) *)
  val mk_bv_s : TermManager.tm -> int -> string -> int -> term

  (** Create a rounding mode value.

      Parameters: - The floating-point rounding mode this constant represents *)
  val mk_rm : TermManager.tm -> RoundingMode.t -> term

  (** Create a floating-point value from a bit-vector given in IEEE-754 format.

      Parameters: - Size of the exponent
      - Size of the significand
      - Value of the floating-point constant as a bit-vector term *)
  val mk_fp : TermManager.tm -> int -> int -> term -> term

  (** Create a floating-point value from its three IEEE-754 bit-vector value
      components (sign bit, exponent, significand)

      Parameters: - The bit-vector representing the sign bit
      - The bit-vector representing the exponent
      - The bit-vector representing the significand *)
  val mk_fp_from_terms : TermManager.tm -> term -> term -> term -> term

  (** Create a positive infinity floating-point constant (SMT-LIB: +oo).

      Parameters: - Number of bits in the exponent
      - Number of bits in the significand *)
  val mk_fp_pos_inf : TermManager.tm -> int -> int -> term

  (** Create a negative infinity floating-point constant (SMT-LIB: -oo).

      Parameters: - Number of bits in the exponent
      - Number of bits in the significand *)
  val mk_fp_neg_inf : TermManager.tm -> int -> int -> term

  (** Create a not-a-number floating-point constant (SMT-LIB: NaN).

      Parameters: - Number of bits in the exponent
      - Number of bits in the significand *)
  val mk_fp_nan : TermManager.tm -> int -> int -> term

  (** Create a positive zero floating-point constant (SMT-LIB: +zero).

      Parameters: - Number of bits in the exponent
      - Number of bits in the significand *)
  val mk_fp_pos_zero : TermManager.tm -> int -> int -> term

  (** Create a negative zero floating-point constant (SMT-LIB: -zero).

      Parameters: - Number of bits in the exponent
      - Number of bits in the significand *)
  val mk_fp_neg_zero : TermManager.tm -> int -> int -> term

  (** Determine if the term is an [int] value. *)
  val is_int : term -> bool

  (** Determine if the term is a real value. *)
  val is_real : term -> bool

  (** Determine if the term is a [string] value. *)
  val is_string : term -> bool

  (** Determine if the term is a [bool] value. *)
  val is_bool : term -> bool

  (** Determine if the term is a [int32] value. *)
  val is_int32 : term -> bool

  (** Determine if the term is a bit-vector value. *)
  val is_bv : term -> bool

  (** Determine if the term is a [int64] value. *)
  val is_int64 : term -> bool

  (** Determine if the term is a uint32 value. *)
  val is_uint32 : term -> bool

  (** Determine if the term is a uint64 value. *)
  val is_uint64 : term -> bool

  (** Determine if the term is a floating-point rounding mode value. *)
  val is_rm : term -> bool

  (** Determine if a given term is a floating-point value. *)
  val is_fp : term -> bool

  (** Get the integer value. *)
  val get_int : term -> int

  (** Get the real value. *)
  val get_real : term -> float

  (** Get the string value. *)
  val get_string : term -> string

  (** Get the Boolean value. *)
  val get_bool : term -> bool

  (** Get the int32 value. *)
  val get_int32 : term -> int32

  (** Get the int64 value. *)
  val get_int64 : term -> int64

  (** Get the uint32 value. *)
  val get_uint32 : term -> int

  (** Get the uint64 value. *)
  val get_uint64 : term -> int

  (** Get the string representation of the bit-vector value.

      Parameters: - Base. [2] for binary, [10] for decimal, and [16] for
      hexadecimal *)
  val get_bv : term -> int -> string

  (** Get the rounding mode value. *)
  val get_rm : term -> RoundingMode.t

  (** Get the representation of a floating-point value as a tuple of its
      exponent width, significand width and a bit-vector value term. *)
  val get_fp : term -> int * int * term
end

module Result : sig
  type result

  (** Result instance destructor. *)
  val delete : result -> unit

  (** Operator overloading for equality of two results. *)
  val equal : result -> result -> bool

  (** Get the string representation of the result. *)
  val to_string : result -> string

  (** Determine if the result is SAT. *)
  val is_sat : result -> bool

  (** Determine if the result is UNSAT. *)
  val is_unsat : result -> bool

  (** Determine if the result is UNKNOWN. *)
  val is_unknown : result -> bool
end

module Grammar : sig
  type grammar

  val add_rules : grammar -> Term.term -> Term.term array -> unit
end

module SynthResult : sig
  type synthresult

  val is_null : synthresult -> bool

  val has_solution : synthresult -> bool

  val has_no_solution : synthresult -> bool

  val is_unknown : synthresult -> bool

  val to_string : synthresult -> string
end

module Solver : sig
  type solver

  (** Solver instance constructor. *)
  val mk_solver : ?logic:string -> TermManager.tm -> solver

  (** Solver instance destructor. *)
  val delete : solver -> unit

  (** Assert a formula to the solver.

      Parameters: - The formula to assert *)
  val assert_formula : solver -> Term.term -> unit

  (** Check satisfiability. *)
  val check_sat : solver -> Result.result

  (** Check satisfiability assuming a set of formulas.

      Parameters: - The set of formulas to assume *)
  val check_sat_assuming : solver -> Term.term array -> Result.result

  (** Set the logic of the solver. *)
  val set_logic : solver -> string -> unit

  (** Set an option of the solver.

      Parameters: - The option to set
      - The value of the option *)
  val set_option : solver -> string -> string -> unit

  (** Simplify a term or formula based on rewriting. *)
  val simplify : solver -> Term.term -> Term.term

  (** Push (a) level(s) to the assertion stack.

      Parameters: - The number of levels to push *)
  val push : solver -> int -> unit

  (** Pop (a) level(s) from the assertion stack.

      Parameters: - The number of levels to pop *)
  val pop : solver -> int -> unit

  (** Reset all assertions. *)
  val reset : solver -> unit

  (** Get the value of the given term in the current model.

      Parameters: - The term for which the value is queried *)
  val get_value : solver -> Term.term -> Term.term

  (** Get the values of the given terms in the current model.

      Parameters: - The terms for which the values is queried *)
  val get_values : solver -> Term.term array -> Term.term array

  (** Get the domain elements of uninterpreted sort s in the current model. The
      current model interprets s as the finite sort whose domain elements are
      given in the return value of this function.

      Parameters: - The uninterpreted sort in question *)
  val get_model_domain_elements : solver -> Sort.sort -> Term.term array

  (** Get the unsatisfiable core. *)
  val get_unsat_core : solver -> Term.term array

  (** Get the model.

      Parameters: - The list of uninterpreted sorts that should be printed in
      the model
      - The list of free constants that should be printed in the model *)
  val get_model : solver -> Sort.sort array -> Term.term array -> string

  (** Declare n-ary function symbol.

      Parameters: - The name of the function
      - The sorts of the parameters of this function
      - the sort of the return value of this function *)
  val declare_fun :
    solver -> string -> Sort.sort array -> Sort.sort -> Term.term

  (** Define n-ary function.

      Parameters: - The name of the function
      - The parameters of this function
      - The sort of the return value of this function
      - The function body *)
  val define_fun :
    solver -> string -> Term.term array -> Sort.sort -> Term.term -> Term.term

  val mk_grammar :
    solver -> Term.term array -> Term.term array -> Grammar.grammar

  val synth_fun :
       solver
    -> TermManager.tm
    -> string
    -> Term.term array
    -> Sort.sort
    -> Grammar.grammar option
    -> Term.term

  val declare_sygus_var : solver -> string -> Sort.sort -> Term.term

  val add_sygus_constraint : solver -> Term.term -> unit

  val add_sygus_assume : solver -> Term.term -> unit

  val check_synth : solver -> SynthResult.synthresult

  val get_synth_solution : solver -> Term.term -> Term.term

  val get_synth_solutions : solver -> Term.term array -> Term.term array
end
