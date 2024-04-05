exception Error of string

module Kind = Cvc5_enums.Kind
module RoundingMode = Cvc5_enums.RoundingMode

module TermManager : sig
  type tm

  val mk_tm : unit -> tm

  val delete_tm : tm -> unit
end

module Sort : sig
  type sort

  val mk_bool_sort : TermManager.tm -> sort

  val mk_int_sort : TermManager.tm -> sort

  val mk_real_sort : TermManager.tm -> sort

  val mk_string_sort : TermManager.tm -> sort

  val mk_bv_sort : TermManager.tm -> int -> sort
end

module Term : sig
  type term

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

  val mk_rm : TermManager.tm -> RoundingMode.t -> term
end

module Result : sig
  type result

  val is_sat : result -> bool

  val is_unsat : result -> bool

  val is_unknown : result -> bool
end

module Solver : sig
  type solver

  val mk_solver : TermManager.tm -> solver

  val delete_solver : solver -> unit

  val assert_formula : solver -> Term.term -> unit

  val check_sat : solver -> Result.result

  val set_logic : solver -> string -> unit

  val simplify : solver -> Term.term -> Term.term

  val push : solver -> int -> unit

  val pop : solver -> int -> unit

  val reset : solver -> unit
end
