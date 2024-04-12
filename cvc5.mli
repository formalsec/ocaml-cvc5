exception Error of string

module Kind = Cvc5_enums.Kind
module RoundingMode = Cvc5_enums.RoundingMode

module TermManager : sig
  type tm

  val mk_tm : unit -> tm

  val delete : tm -> unit
end

module Sort : sig
  type sort

  val delete : sort -> unit

  val equal : sort -> sort -> bool

  val to_string : sort -> string

  val mk_bool_sort : TermManager.tm -> sort

  val mk_int_sort : TermManager.tm -> sort

  val mk_real_sort : TermManager.tm -> sort

  val mk_string_sort : TermManager.tm -> sort

  val mk_bv_sort : TermManager.tm -> int -> sort

  val bv_size : sort -> int32

  val mk_rm_sort : TermManager.tm -> sort

  val mk_fp_sort : TermManager.tm -> int -> int -> sort

  val mk_seq_sort : TermManager.tm -> sort -> sort

  val mk_uninterpreted_sort : TermManager.tm -> string -> sort
end

module Term : sig
  type term

  val delete : term -> unit

  val id : term -> int

  val equal : term -> term -> bool

  val kind : term -> Kind.t

  val sort : term -> Sort.sort

  val to_string : term -> string

  val mk_const : TermManager.tm -> Sort.sort -> term

  val mk_const_s : TermManager.tm -> Sort.sort -> string -> term

  val mk_term : TermManager.tm -> Kind.t -> term array -> term

  val mk_true : TermManager.tm -> term

  val mk_false : TermManager.tm -> term

  val mk_bool : TermManager.tm -> bool -> term

  val mk_int : TermManager.tm -> int -> term

  val mk_string : TermManager.tm -> ?useEscSequences:bool -> string -> term

  val mk_real_s : TermManager.tm -> string -> term

  val mk_real_i : TermManager.tm -> int -> term

  val mk_real : TermManager.tm -> int -> int -> term

  val mk_bv : TermManager.tm -> int32 -> int64 -> term

  val mk_bv_s : TermManager.tm -> int32 -> string -> int32 -> term

  val mk_rm : TermManager.tm -> RoundingMode.t -> term

  val mk_fp : TermManager.tm -> int32 -> int32 -> term -> term

  val is_int : term -> bool

  val is_real : term -> bool

  val is_string : term -> bool

  val is_bool : term -> bool

  val is_int32 : term -> bool

  val is_bv : term -> bool

  val is_int64 : term -> bool

  val is_uint32 : term -> bool

  val is_uint64 : term -> bool

  val is_rm : term -> bool

  val get_int : term -> int

  val get_real : term -> float

  val get_bool : term -> bool

  val get_int32 : term -> int32

  val get_int64 : term -> int64

  val get_uint32 : term -> int32

  val get_uint64 : term -> int64

  val get_bv : term -> int32 -> string

  val get_rm : term -> RoundingMode.t
end

module Result : sig
  type result

  val delete : result -> unit

  val equal : result -> result -> bool

  val to_string : result -> string

  val is_sat : result -> bool

  val is_unsat : result -> bool

  val is_unknown : result -> bool
end

module Solver : sig
  type solver

  val mk_solver : TermManager.tm -> solver

  val delete : solver -> unit

  val assert_formula : solver -> Term.term -> unit

  val check_sat : solver -> Result.result

  val check_sat_assuming : solver -> Term.term array -> Result.result

  val set_logic : solver -> string -> unit

  val set_option : solver -> string -> string -> unit

  val simplify : solver -> Term.term -> Term.term

  val push : solver -> int -> unit

  val pop : solver -> int -> unit

  val reset : solver -> unit

  val get_value : solver -> Term.term -> Term.term

  val get_values : solver -> Term.term array -> Term.term array

  val get_model_domain_elements : solver -> Sort.sort -> Term.term array

  val get_unsat_core : solver -> Term.term array

  val get_model : solver -> Sort.sort array -> Term.term array -> string
end
