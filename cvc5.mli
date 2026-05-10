(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

exception Error of string

module Kind = Cvc5_enums.Kind
module RoundingMode = Cvc5_enums.RoundingMode
module UnknownExplanation = Cvc5_enums.UnknownExplanation
module BlockModelsMode = Cvc5_enums.BlockModelsMode
module LearnedLitType = Cvc5_enums.LearnedLitType
module ProofComponent = Cvc5_enums.ProofComponent
module ProofFormat = Cvc5_enums.ProofFormat
module FindSynthTarget = Cvc5_enums.FindSynthTarget
module OptionCategory = Cvc5_enums.OptionCategory
module InputLanguage = Cvc5_enums.InputLanguage

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

  (** Create a parameter sort.

      Parameters: - The name of the sort. *)
  val mk_param_sort : TermManager.tm -> ?name:string -> unit -> sort

  (** Create an unresolved datatype sort.

      This is for creating yet unresolved sort placeholders for mutually recursive parametric datatypes.
      Parameters: - The symbol of the sort
      - The number of sort parameters of the sort *)
  val mk_unresolved_datatype_sort : TermManager.tm -> string -> int -> sort

  (** Determine if this is the null sort.*)
  val is_null : sort -> bool

  (** Determine if this is the boolean sort (SMT-LIB: Bool). *)
  val is_bool : sort -> bool

  (** Determine if this is the integer sort (SMT-LIB: Int). *)
  val is_int : sort -> bool

  (** Determine if this is the real sort (SMT-LIB: Real). *)
  val is_real : sort -> bool

  (** Determine if this is the string sort (SMT-LIB: String). *)
  val is_string : sort -> bool

  (** Determine if this is the regular expression sort (SMT-LIB: RegLan). *)
  val is_regexp : sort -> bool

  (** Determine if this is the rounding mode sort (SMT-LIB: RoundingMode). *)
  val is_rm : sort -> bool

  (** Determine if this is a bit-vector sort (SMT-LIB: _ BitVec i). *)
  val is_bv : sort -> bool

  (** Determine if this is a floating-point sort (SMT-LIB: _ FloatingPoint eb sb). *)
  val is_fp : sort -> bool

  (** Determine if this is a datatype sort. *)
  val is_datatype : sort -> bool

  (** Determine if this is a datatype constructor sort. *)
  val is_datatype_constructor : sort -> bool

  (** Determine if this is a datatype selector sort. *)
  val is_datatype_selector : sort -> bool

  (** Determine if this is a datatype tester sort. *)
  val is_datatype_tester : sort -> bool

  (** Determine if this is a function sort. *)
  val is_fun : sort -> bool

  (** Determine if this is a predicate sort. 
    
      A predicate sort is a function sort that maps to the Boolean sort. 
      All predicate sorts are also function sorts. *)
  val is_pred : sort -> bool

  (** Determine if this is a tuple sort. *)
  val is_tuple : sort -> bool

  (** Determine if this is a nullable sort. *)
  val is_nullable : sort -> bool

  (** Determine if this is a record sort. *)
  val is_record : sort -> bool

  (** Determine if this is an array sort. *)
  val is_array : sort -> bool

  (** Determine if this is a finite field sort. *)
  val is_finite_field : sort -> bool

  (** Determine if this is a Set sort. *)
  val is_set : sort -> bool

  (** Determine if this is a Bag sort. *)
  val is_bag : sort -> bool

  (** Determine if this is a Sequence sort. *)
  val is_seq : sort -> bool

  (** Determine if this is an abstract sort. *)
  val is_abstract : sort -> bool

  (** Determine if this is an uninterpreted sort. *)
  val is_uninterpreted : sort -> bool

  (** Determine if this is an uninterpreted sort constructor. 
    
      An uninterpreted sort constructor has arity > 0 and can be instantiated 
      to construct uninterpreted sorts with given sort parameters.*)
  val is_uninterpreted_sort_constructor : sort -> bool

  (** Determine if this is an instantiated 
      (parametric datatype or uninterpreted sort constructor) sort.
    
      An instantiated sort is a sort that has been constructed 
      from instantiating a sort with sort arguments. *)
  val is_instantiated : sort -> bool

  (** Get the associated uninterpreted sort constructor of an instantiated uninterpreted sort. *)
  val get_uninterpreted_sort_constructor : sort -> sort

  (** Instantiate a parameterized datatype sort or uninterpreted sort constructor sort. *)
  val instantiate : sort -> sort array -> sort

  (** Get the sorts used to instantiate the sort parameters of 
      a parametric sort (parametric datatype or uninterpreted sort constructor sort) *)
  val get_instantiated_parameters : sort -> sort array

  (** Substitution of Sorts.

      Note that this replacement is applied during a pre-order traversal and only once to the sort. It is not run until fix point.
      For example, (Array A B).substitute({A, C}, {(Array C D), (Array A B)}) 
      will return (Array (Array C D) B). *)
  val substitute : sort -> sort -> sort -> sort

  (** Simultaneous substitution of Sorts.

      Note that this replacement is applied during a pre-order traversal and only once to the sort. 
      It is not run until fix point. In the case that sorts contains duplicates, 
      the replacement earliest in the vector takes priority.
  *)
  val substitute_many : sort -> sort array -> sort array -> sort
end

module Op : sig
  type op
  type term

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

  val get_index : op -> int -> term

  (** Get the kind of the operator. *)
  val kind : op -> Kind.t

  (** Hash function for Ops. *)
  val hash : op -> int

  (** Get the number of indices of the operator. *)
  val get_num_indices : op -> int
end

module Term : sig
  type term = Op.term

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

  val get_num_children : term -> int

  val get_child : term -> int -> term

  val substitute : term -> term -> term -> term

  val substitute_many : term -> term array -> term array -> term

  val has_op : term -> bool

  val get_op : term -> Op.op

  val has_symbol : term -> bool

  val get_symbol : term -> string

  val is_null : term -> bool

  val not_term : term -> term

  val and_term : term -> term -> term

  val or_term : term -> term -> term

  val xor_term : term -> term -> term

  val eq_term : term -> term -> term

  val imp_term : term -> term -> term

  val ite_term : term -> term -> term -> term
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

  val is_null : result -> bool

  val get_unknown_explanation : result -> UnknownExplanation.t
end

module Grammar : sig
  type grammar

  val add_rule : grammar -> Term.term -> Term.term -> unit

  val add_rules : grammar -> Term.term -> Term.term array -> unit

  val add_any_constant : grammar -> Term.term -> unit

  val add_any_variable : grammar -> Term.term -> unit

  val is_null : grammar -> bool

  val to_string : grammar -> string
end

module SynthResult : sig
  type synthresult

  val is_null : synthresult -> bool

  val has_solution : synthresult -> bool

  val has_no_solution : synthresult -> bool

  val is_unknown : synthresult -> bool

  val to_string : synthresult -> string
end

module DatatypeConstructorDecl : sig
  type datatype_constructor_decl

  val mk : TermManager.tm -> string -> datatype_constructor_decl

  val delete : datatype_constructor_decl -> unit

  val equal :
    datatype_constructor_decl -> datatype_constructor_decl -> bool

  val add_selector : datatype_constructor_decl -> string -> Sort.sort -> unit

  val add_selector_self : datatype_constructor_decl -> string -> unit

  val add_selector_unresolved :
    datatype_constructor_decl -> string -> string -> unit

  val is_null : datatype_constructor_decl -> bool

  val to_string : datatype_constructor_decl -> string
end

module DatatypeDecl : sig
  type datatype_decl

  val mk :
       ?params:Sort.sort array
    -> ?isCoDatatype:bool
    -> TermManager.tm
    -> string
    -> datatype_decl

  val delete : datatype_decl -> unit

  val equal : datatype_decl -> datatype_decl -> bool

  val add_constructor :
    datatype_decl -> DatatypeConstructorDecl.datatype_constructor_decl -> unit

  val get_num_constructors : datatype_decl -> int

  val is_parametric : datatype_decl -> bool

  val is_resolved : datatype_decl -> bool

  val is_null : datatype_decl -> bool

  val to_string : datatype_decl -> string

  val get_name : datatype_decl -> string
end

module DatatypeSelector : sig
  type datatype_selector

  val delete : datatype_selector -> unit

  val equal : datatype_selector -> datatype_selector -> bool

  val get_name : datatype_selector -> string

  val get_term : datatype_selector -> Term.term

  val get_updater_term : datatype_selector -> Term.term

  val get_codomain_sort : datatype_selector -> Sort.sort

  val is_null : datatype_selector -> bool

  val to_string : datatype_selector -> string
end

module DatatypeConstructor : sig
  type datatype_constructor

  val delete : datatype_constructor -> unit

  val equal : datatype_constructor -> datatype_constructor -> bool

  val get_name : datatype_constructor -> string

  val get_term : datatype_constructor -> Term.term

  val get_instantiated_term : datatype_constructor -> Sort.sort -> Term.term

  val get_tester_term : datatype_constructor -> Term.term

  val get_num_selectors : datatype_constructor -> int

  val get_selector_at :
    datatype_constructor -> int -> DatatypeSelector.datatype_selector

  val get_selector :
    datatype_constructor -> string -> DatatypeSelector.datatype_selector

  val is_null : datatype_constructor -> bool

  val to_string : datatype_constructor -> string
end

module Datatype : sig
  type datatype

  val of_sort : Sort.sort -> datatype

  val delete : datatype -> unit

  val equal : datatype -> datatype -> bool

  val get_constructor_at :
    datatype -> int -> DatatypeConstructor.datatype_constructor

  val get_constructor :
    datatype -> string -> DatatypeConstructor.datatype_constructor

  val get_selector : datatype -> string -> DatatypeSelector.datatype_selector

  val get_name : datatype -> string

  val get_num_constructors : datatype -> int

  val get_parameters : datatype -> Sort.sort array

  val is_parametric : datatype -> bool

  val is_codatatype : datatype -> bool

  val is_tuple : datatype -> bool

  val is_record : datatype -> bool

  val is_finite : datatype -> bool

  val is_well_founded : datatype -> bool

  val is_null : datatype -> bool

  val to_string : datatype -> string
end

module Proof : sig
  type proof

  val delete : proof -> unit

  val equal : proof -> proof -> bool

  val is_null : proof -> bool

  val get_result : proof -> Term.term

  val get_children : proof -> proof array

  val get_arguments : proof -> Term.term array
end

module OptionInfo : sig
  type option_info

  val delete : option_info -> unit

  val to_string : option_info -> string

  val name : option_info -> string

  val aliases : option_info -> string array

  val no_supports : option_info -> string array

  val set_by_user : option_info -> bool

  val category : option_info -> OptionCategory.t

  val is_bool : option_info -> bool

  val is_string : option_info -> bool

  val is_int : option_info -> bool

  val is_uint : option_info -> bool

  val is_double : option_info -> bool

  val is_mode : option_info -> bool

  val bool_value : option_info -> bool

  val string_value : option_info -> string

  val int_value : option_info -> int64

  val uint_value : option_info -> int64

  val double_value : option_info -> float
end

module Stat : sig
  type stat

  val delete : stat -> unit

  val to_string : stat -> string

  val is_internal : stat -> bool

  val is_default : stat -> bool

  val is_int : stat -> bool

  val get_int : stat -> int64

  val is_double : stat -> bool

  val get_double : stat -> float

  val is_string : stat -> bool

  val get_string : stat -> string

  val is_histogram : stat -> bool

  val get_histogram : stat -> (string * int64) array
end

module Statistics : sig
  type statistics

  val of_term_manager : TermManager.tm -> statistics

  val delete : statistics -> unit

  val to_string : statistics -> string

  val get : statistics -> string -> Stat.stat

  val entries : statistics -> (string * Stat.stat) array
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

  val set_info : solver -> string -> string -> unit

  (** Set the logic of the solver. *)
  val set_logic : solver -> string -> unit

  val is_logic_set : solver -> bool

  val get_logic : solver -> string

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

  val get_assertions : solver -> Term.term array

  val get_info : solver -> string -> string

  val get_option : solver -> string -> string

  val get_option_names : solver -> string array

  val get_option_info : solver -> string -> OptionInfo.option_info

  val get_unsat_assumptions : solver -> Term.term array

  val get_unsat_core_lemmas : solver -> Term.term array

  val get_difficulty : solver -> (Term.term * Term.term) array

  val get_timeout_core : solver -> Result.result * Term.term array

  val get_timeout_core_assuming :
    solver -> Term.term array -> Result.result * Term.term array

  val get_proof : ?component:ProofComponent.t -> solver -> Proof.proof array

  val proof_to_string :
    ?format:ProofFormat.t -> solver -> Proof.proof -> string

  val get_learned_literals :
    ?kind:LearnedLitType.t -> solver -> Term.term array

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

  val declare_sort : ?fresh:bool -> solver -> string -> int -> Sort.sort

  val declare_datatype :
    solver
    -> string
    -> DatatypeConstructorDecl.datatype_constructor_decl array
    -> Sort.sort

  (** Define n-ary function.

      Parameters: - The name of the function
      - The parameters of this function
      - The sort of the return value of this function
      - The function body *)
  val define_fun :
    solver -> string -> Term.term array -> Sort.sort -> Term.term -> Term.term

  val define_fun_rec :
       ?global:bool
    -> solver
    -> string
    -> Term.term array
    -> Sort.sort
    -> Term.term
    -> Term.term

  val define_fun_rec_term :
       ?global:bool
    -> solver
    -> Term.term
    -> Term.term array
    -> Term.term
    -> Term.term

  val define_funs_rec :
       ?global:bool
    -> solver
    -> Term.term array
    -> Term.term array array
    -> Term.term array
    -> unit

  val get_quantifier_elimination : solver -> Term.term -> Term.term

  val get_quantifier_elimination_disjunct : solver -> Term.term -> Term.term

  val declare_sep_heap : solver -> Sort.sort -> Sort.sort -> unit

  val get_value_sep_heap : solver -> Term.term

  val get_value_sep_nil : solver -> Term.term

  val declare_pool :
    solver -> string -> Sort.sort -> Term.term array -> Term.term

  val block_model : ?mode:BlockModelsMode.t -> solver -> unit

  val block_model_values : solver -> Term.term array -> unit

  val get_instantiations : solver -> string

  val get_interpolant :
    ?grammar:Grammar.grammar -> solver -> Term.term -> Term.term

  val get_interpolant_next : solver -> Term.term

  val get_abduct :
    ?grammar:Grammar.grammar -> solver -> Term.term -> Term.term

  val get_abduct_next : solver -> Term.term

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

  val get_sygus_constraints : solver -> Term.term array

  val add_sygus_assume : solver -> Term.term -> unit

  val get_sygus_assumptions : solver -> Term.term array

  val add_sygus_inv_constraint :
    solver -> Term.term -> Term.term -> Term.term -> Term.term -> unit

  val check_synth : solver -> SynthResult.synthresult

  val check_synth_next : solver -> SynthResult.synthresult

  val get_synth_solution : solver -> Term.term -> Term.term

  val get_synth_solutions : solver -> Term.term array -> Term.term array

  val find_synth :
    ?grammar:Grammar.grammar -> solver -> FindSynthTarget.t -> Term.term

  val get_statistics : solver -> Statistics.statistics
end
