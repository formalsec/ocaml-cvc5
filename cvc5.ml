(* SPDX-License-Identifier: MIT *)
(* Copyright (C) 2024-2025 formalsec *)
(* Written by Joao Pereira *)

exception Error of string

let _ = Callback.register_exception "cvc5Exception" (Error "")

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

module TermManager = struct
  type tm = Cvc5_external.term_manager

  let mk_tm = Cvc5_external.new_term_manager

  let delete = Cvc5_external.delete_term_manager
end

module Sort = struct
  type sort = Cvc5_external.sort

  let equal = Cvc5_external.sort_equal

  let delete = Cvc5_external.delete_sort

  let to_string = Cvc5_external.sort_to_string

  let mk_bool_sort = Cvc5_external.get_boolean_sort

  let mk_int_sort = Cvc5_external.get_integer_sort

  let mk_real_sort = Cvc5_external.get_real_sort

  let mk_string_sort = Cvc5_external.get_string_sort

  let mk_regexp_sort = Cvc5_external.get_regexp_sort

  let mk_bv_sort = Cvc5_external.mk_bitvector_sort

  let bv_size = Cvc5_external.sort_get_bv_size

  let mk_rm_sort = Cvc5_external.get_rm_sort

  let mk_fp_sort = Cvc5_external.mk_fp_sort

  let mk_seq_sort = Cvc5_external.mk_seq_sort

  let mk_uninterpreted_sort = Cvc5_external.mk_uninterpreted_sort

  let mk_param_sort tm ?name () = Cvc5_external.tm_mk_param_sort tm name

  let mk_unresolved_datatype_sort = Cvc5_external.tm_mk_unresolved_datatype_sort

  let is_null = Cvc5_external.sort_is_null

  let is_bool = Cvc5_external.sort_is_boolean

  let is_int = Cvc5_external.sort_is_integer

  let is_real = Cvc5_external.sort_is_real

  let is_string = Cvc5_external.sort_is_string

  let is_regexp = Cvc5_external.sort_is_regexp

  let is_rm = Cvc5_external.sort_is_rm

  let is_bv = Cvc5_external.sort_is_bv

  let is_fp = Cvc5_external.sort_is_fp

  let is_datatype = Cvc5_external.sort_is_datatype

  let is_datatype_constructor = Cvc5_external.sort_is_datatype_constructor

  let is_datatype_selector = Cvc5_external.sort_is_datatype_selector

  let is_datatype_tester = Cvc5_external.sort_is_datatype_tester

  let is_fun = Cvc5_external.sort_is_function

  let is_pred = Cvc5_external.sort_is_predicate

  let is_tuple = Cvc5_external.sort_is_tuple

  let is_nullable = Cvc5_external.sort_is_nullable

  let is_record = Cvc5_external.sort_is_record

  let is_array = Cvc5_external.sort_is_array

  let is_finite_field = Cvc5_external.sort_is_finite_field

  let is_set = Cvc5_external.sort_is_set

  let is_bag = Cvc5_external.sort_is_bag

  let is_seq = Cvc5_external.sort_is_sequence

  let is_abstract = Cvc5_external.sort_is_abstract

  let is_uninterpreted = Cvc5_external.sort_is_uninterpreted_sort

  let is_uninterpreted_sort_constructor =
    Cvc5_external.sort_is_uninterpreted_sort_constructor

  let is_instantiated = Cvc5_external.sort_is_instantiated

  let get_uninterpreted_sort_constructor =
    Cvc5_external.sort_get_uninterpreted_sort_constructor

  let instantiate = Cvc5_external.sort_instantiate

  let get_instantiated_parameters =
    Cvc5_external.sort_get_instantiated_parameters

  let substitute = Cvc5_external.sort_substitute

  let substitute_many = Cvc5_external.sort_substitute_many
end

module Op = struct
  type op = Cvc5_external.op
  type term = Cvc5_external.term

  let mk_op tm kind args = Cvc5_external.mk_op tm (Kind.to_cpp kind) args

  let equal = Cvc5_external.op_equal

  let delete = Cvc5_external.op_delete

  let to_string = Cvc5_external.op_to_string

  let is_indexed = Cvc5_external.op_is_indexed

  let get_index = Cvc5_external.op_get_index

  let kind o = Kind.of_cpp @@ Cvc5_external.op_get_kind o

  let hash = Cvc5_external.op_hash

  let get_num_indices = Cvc5_external.op_get_num_indices
end

module Term = struct
  type term = Op.term

  let id = Cvc5_external.term_id

  let delete = Cvc5_external.delete_term

  let equal = Cvc5_external.term_equal

  let kind t = Kind.of_cpp @@ Cvc5_external.term_kind t

  let sort = Cvc5_external.term_sort

  let to_string = Cvc5_external.term_to_string

  let mk_const = Cvc5_external.mk_const

  let mk_const_s = Cvc5_external.mk_const_s

  let mk_var = Cvc5_external.mk_var

  let mk_var_s = Cvc5_external.mk_var_s

  let mk_term (tm : TermManager.tm) (k : Kind.t) (terms : term array) =
    Cvc5_external.mk_term tm (Kind.to_cpp k) terms

  let mk_term_1 (tm : TermManager.tm) (k : Kind.t) (t1 : term) =
    Cvc5_external.mk_term_1 tm (Kind.to_cpp k) t1

  let mk_term_2 (tm : TermManager.tm) (k : Kind.t) (t1 : term) (t2 : term) =
    Cvc5_external.mk_term_2 tm (Kind.to_cpp k) t1 t2

  let mk_term_3 (tm : TermManager.tm) (k : Kind.t) (t1 : term) (t2 : term)
    (t3 : term) =
    Cvc5_external.mk_term_3 tm (Kind.to_cpp k) t1 t2 t3

  let mk_term_op (tm : TermManager.tm) (op : Op.op) (terms : term array) =
    Cvc5_external.mk_term_op tm op terms

  let mk_true = Cvc5_external.mk_true

  let mk_false = Cvc5_external.mk_false

  let mk_bool = Cvc5_external.mk_bool

  let mk_int = Cvc5_external.mk_int

  let mk_string tm ?(useEscSequences = false) s =
    Cvc5_external.mk_string tm s useEscSequences

  let mk_real_s = Cvc5_external.mk_real_s

  let mk_real_i = Cvc5_external.mk_real_i

  let mk_real = Cvc5_external.mk_real

  let mk_bv = Cvc5_external.mk_bv

  let mk_bv_s = Cvc5_external.mk_bv_s

  let mk_rm (tm : TermManager.tm) (rm : RoundingMode.t) =
    Cvc5_external.mk_roundingmode tm (RoundingMode.to_cpp rm)

  let mk_fp = Cvc5_external.mk_fp

  let mk_fp_from_terms = Cvc5_external.mk_fp_terms

  let mk_fp_pos_inf = Cvc5_external.mk_fp_pos_inf

  let mk_fp_neg_inf = Cvc5_external.mk_fp_neg_inf

  let mk_fp_nan = Cvc5_external.mk_fp_nan

  let mk_fp_pos_zero = Cvc5_external.mk_fp_pos_zero

  let mk_fp_neg_zero = Cvc5_external.mk_fp_neg_zero

  let is_int = Cvc5_external.term_is_int_val

  let is_real = Cvc5_external.term_is_real_val

  let is_string = Cvc5_external.term_is_string_val

  let is_bv = Cvc5_external.term_is_bv_val

  let is_int32 = Cvc5_external.term_is_int32_val

  let is_int64 = Cvc5_external.term_is_int64_val

  let is_uint32 = Cvc5_external.term_is_uint32_val

  let is_uint64 = Cvc5_external.term_is_uint64_val

  let is_rm = Cvc5_external.term_is_rm_val

  let is_fp = Cvc5_external.term_is_fp_val

  let is_bool = Cvc5_external.term_is_bool_val

  let get_int t = int_of_string (Cvc5_external.term_get_int_val t)

  let get_real t =
    let real_str = Cvc5_external.term_get_real_val t in
    (* cvc5 returns string of float in fraction format *)
    let fraction_to_float str =
      match String.split_on_char '/' str with
      | [ numerator; denominator ] ->
        let num = float_of_string numerator in
        let denom = float_of_string denominator in
        num /. denom
      | _ -> assert false
    in
    fraction_to_float real_str

  let get_string = Cvc5_external.term_get_string_val

  let get_int32 = Cvc5_external.term_get_int32_val

  let get_int64 = Cvc5_external.term_get_int64_val

  let get_bv = Cvc5_external.term_get_bv_val

  let get_uint32 = Cvc5_external.term_get_uint32_val

  let get_uint64 = Cvc5_external.term_get_uint64_val

  let get_rm t = RoundingMode.of_cpp @@ Cvc5_external.term_get_rm_val t

  let get_fp = Cvc5_external.term_get_fp_val

  let get_bool = Cvc5_external.term_get_bool_val

  let get_num_children = Cvc5_external.term_get_num_children

  let get_child = Cvc5_external.term_get_child

  let substitute = Cvc5_external.term_substitute

  let substitute_many = Cvc5_external.term_substitute_many

  let has_op = Cvc5_external.term_has_op

  let get_op = Cvc5_external.term_get_op

  let has_symbol = Cvc5_external.term_has_symbol

  let get_symbol = Cvc5_external.term_get_symbol

  let is_null = Cvc5_external.term_is_null

  let not_term = Cvc5_external.term_not_term

  let and_term = Cvc5_external.term_and_term

  let or_term = Cvc5_external.term_or_term

  let xor_term = Cvc5_external.term_xor_term

  let eq_term = Cvc5_external.term_eq_term

  let imp_term = Cvc5_external.term_imp_term

  let ite_term = Cvc5_external.term_ite_term
end

module Result = struct
  type result = Cvc5_external.result

  let delete = Cvc5_external.delete_result

  let equal = Cvc5_external.result_equal

  let to_string = Cvc5_external.result_to_string

  let is_sat = Cvc5_external.result_is_sat

  let is_unsat = Cvc5_external.result_is_unsat

  let is_unknown = Cvc5_external.result_is_unknown

  let is_null = Cvc5_external.result_is_null

  let get_unknown_explanation t =
    UnknownExplanation.of_cpp @@ Cvc5_external.result_get_unknown_explanation t
end

module Grammar = struct
  type grammar = Cvc5_external.grammar

  let add_rule = Cvc5_external.grammar_add_rule

  let add_rules = Cvc5_external.grammar_add_rules

  let add_any_constant = Cvc5_external.grammar_add_any_constant

  let add_any_variable = Cvc5_external.grammar_add_any_variable

  let is_null = Cvc5_external.grammar_is_null

  let to_string = Cvc5_external.grammar_to_string
end

module SynthResult = struct
  type synthresult = Cvc5_external.synthresult

  let is_null = Cvc5_external.synth_is_null

  let has_solution = Cvc5_external.synth_has_solution

  let has_no_solution = Cvc5_external.synth_has_no_solution

  let is_unknown = Cvc5_external.synth_is_unknown

  let to_string = Cvc5_external.synth_to_string
end

module DatatypeConstructorDecl = struct
  type datatype_constructor_decl = Cvc5_external.datatype_constructor_decl

  let mk = Cvc5_external.tm_mk_datatype_constructor_decl

  let delete = Cvc5_external.delete_datatype_constructor_decl

  let equal = Cvc5_external.datatype_constructor_decl_equal

  let add_selector = Cvc5_external.datatype_constructor_decl_add_selector

  let add_selector_self =
    Cvc5_external.datatype_constructor_decl_add_selector_self

  let add_selector_unresolved =
    Cvc5_external.datatype_constructor_decl_add_selector_unresolved

  let is_null = Cvc5_external.datatype_constructor_decl_is_null

  let to_string = Cvc5_external.datatype_constructor_decl_to_string
end

module DatatypeDecl = struct
  type datatype_decl = Cvc5_external.datatype_decl

  let mk ?params ?(isCoDatatype = false) tm name =
    match params with
    | None -> Cvc5_external.tm_mk_datatype_decl tm name isCoDatatype
    | Some params ->
      Cvc5_external.tm_mk_datatype_decl_with_params tm name params isCoDatatype

  let delete = Cvc5_external.delete_datatype_decl

  let equal = Cvc5_external.datatype_decl_equal

  let add_constructor = Cvc5_external.datatype_decl_add_constructor

  let get_num_constructors = Cvc5_external.datatype_decl_get_num_constructors

  let is_parametric = Cvc5_external.datatype_decl_is_parametric

  let is_resolved = Cvc5_external.datatype_decl_is_resolved

  let is_null = Cvc5_external.datatype_decl_is_null

  let to_string = Cvc5_external.datatype_decl_to_string

  let get_name = Cvc5_external.datatype_decl_get_name
end

module DatatypeSelector = struct
  type datatype_selector = Cvc5_external.datatype_selector

  let delete = Cvc5_external.delete_datatype_selector

  let equal = Cvc5_external.datatype_selector_equal

  let get_name = Cvc5_external.datatype_selector_get_name

  let get_term = Cvc5_external.datatype_selector_get_term

  let get_updater_term = Cvc5_external.datatype_selector_get_updater_term

  let get_codomain_sort = Cvc5_external.datatype_selector_get_codomain_sort

  let is_null = Cvc5_external.datatype_selector_is_null

  let to_string = Cvc5_external.datatype_selector_to_string
end

module DatatypeConstructor = struct
  type datatype_constructor = Cvc5_external.datatype_constructor

  let delete = Cvc5_external.delete_datatype_constructor

  let equal = Cvc5_external.datatype_constructor_equal

  let get_name = Cvc5_external.datatype_constructor_get_name

  let get_term = Cvc5_external.datatype_constructor_get_term

  let get_instantiated_term =
    Cvc5_external.datatype_constructor_get_instantiated_term

  let get_tester_term = Cvc5_external.datatype_constructor_get_tester_term

  let get_num_selectors = Cvc5_external.datatype_constructor_get_num_selectors

  let get_selector_at = Cvc5_external.datatype_constructor_get_selector_at

  let get_selector = Cvc5_external.datatype_constructor_get_selector

  let is_null = Cvc5_external.datatype_constructor_is_null

  let to_string = Cvc5_external.datatype_constructor_to_string
end

module Datatype = struct
  type datatype = Cvc5_external.datatype

  let of_sort = Cvc5_external.sort_get_datatype

  let delete = Cvc5_external.delete_datatype

  let equal = Cvc5_external.datatype_equal

  let get_constructor_at = Cvc5_external.datatype_get_constructor_at

  let get_constructor = Cvc5_external.datatype_get_constructor

  let get_selector = Cvc5_external.datatype_get_selector

  let get_name = Cvc5_external.datatype_get_name

  let get_num_constructors = Cvc5_external.datatype_get_num_constructors

  let get_parameters = Cvc5_external.datatype_get_parameters

  let is_parametric = Cvc5_external.datatype_is_parametric

  let is_codatatype = Cvc5_external.datatype_is_codatatype

  let is_tuple = Cvc5_external.datatype_is_tuple

  let is_record = Cvc5_external.datatype_is_record

  let is_finite = Cvc5_external.datatype_is_finite

  let is_well_founded = Cvc5_external.datatype_is_well_founded

  let is_null = Cvc5_external.datatype_is_null

  let to_string = Cvc5_external.datatype_to_string
end

module Proof = struct
  type proof = Cvc5_external.proof

  let delete = Cvc5_external.delete_proof

  let equal = Cvc5_external.proof_equal

  let is_null = Cvc5_external.proof_is_null

  let get_result = Cvc5_external.proof_get_result

  let get_children = Cvc5_external.proof_get_children

  let get_arguments = Cvc5_external.proof_get_arguments
end

module OptionInfo = struct
  type option_info = Cvc5_external.option_info

  let delete = Cvc5_external.delete_option_info

  let to_string = Cvc5_external.option_info_to_string

  let name = Cvc5_external.option_info_name

  let aliases = Cvc5_external.option_info_aliases

  let no_supports = Cvc5_external.option_info_no_supports

  let set_by_user = Cvc5_external.option_info_set_by_user

  let category oi =
    OptionCategory.of_cpp @@ Cvc5_external.option_info_category oi

  let is_bool = Cvc5_external.option_info_is_bool

  let is_string = Cvc5_external.option_info_is_string

  let is_int = Cvc5_external.option_info_is_int

  let is_uint = Cvc5_external.option_info_is_uint

  let is_double = Cvc5_external.option_info_is_double

  let is_mode = Cvc5_external.option_info_is_mode

  let bool_value = Cvc5_external.option_info_bool_value

  let string_value = Cvc5_external.option_info_string_value

  let int_value = Cvc5_external.option_info_int_value

  let uint_value = Cvc5_external.option_info_uint_value

  let double_value = Cvc5_external.option_info_double_value
end

module Stat = struct
  type stat = Cvc5_external.stat

  let delete = Cvc5_external.delete_stat

  let to_string = Cvc5_external.stat_to_string

  let is_internal = Cvc5_external.stat_is_internal

  let is_default = Cvc5_external.stat_is_default

  let is_int = Cvc5_external.stat_is_int

  let get_int = Cvc5_external.stat_get_int

  let is_double = Cvc5_external.stat_is_double

  let get_double = Cvc5_external.stat_get_double

  let is_string = Cvc5_external.stat_is_string

  let get_string = Cvc5_external.stat_get_string

  let is_histogram = Cvc5_external.stat_is_histogram

  let get_histogram = Cvc5_external.stat_get_histogram
end

module Statistics = struct
  type statistics = Cvc5_external.statistics

  let of_term_manager = Cvc5_external.tm_get_statistics

  let of_solver = Cvc5_external.solver_get_statistics

  let delete = Cvc5_external.delete_statistics

  let to_string = Cvc5_external.statistics_to_string

  let get = Cvc5_external.statistics_get

  let entries = Cvc5_external.statistics_entries
end

module Solver = struct
  type solver = Cvc5_external.solver

  let mk_solver ?logic tm =
    let slv = Cvc5_external.new_solver tm in
    match logic with
    | None -> slv
    | Some logic ->
      Cvc5_external.set_logic slv logic;
      slv

  let delete = Cvc5_external.delete

  let assert_formula = Cvc5_external.assert_formula

  let check_sat = Cvc5_external.check_sat

  let check_sat_assuming = Cvc5_external.check_sat_assuming

  let set_info = Cvc5_external.set_info

  let set_logic = Cvc5_external.set_logic

  let is_logic_set = Cvc5_external.solver_is_logic_set

  let get_logic = Cvc5_external.solver_get_logic

  let set_option = Cvc5_external.set_option

  let simplify = Cvc5_external.simplify

  let push = Cvc5_external.push

  let pop = Cvc5_external.pop

  let reset = Cvc5_external.reset_assertions

  let get_value = Cvc5_external.solver_get_value

  let get_values = Cvc5_external.solver_get_values

  let get_model_domain_elements = Cvc5_external.solver_get_model_domain_elements

  let get_unsat_core = Cvc5_external.solver_get_unsat_core

  let get_assertions = Cvc5_external.solver_get_assertions

  let get_info = Cvc5_external.solver_get_info

  let get_option = Cvc5_external.solver_get_option

  let get_option_names = Cvc5_external.solver_get_option_names

  let get_option_info = Cvc5_external.solver_get_option_info

  let get_unsat_assumptions = Cvc5_external.solver_get_unsat_assumptions

  let get_unsat_core_lemmas = Cvc5_external.solver_get_unsat_core_lemmas

  let get_difficulty = Cvc5_external.solver_get_difficulty

  let get_timeout_core = Cvc5_external.solver_get_timeout_core

  let get_timeout_core_assuming = Cvc5_external.solver_get_timeout_core_assuming

  let get_proof ?(component = ProofComponent.Full) solver =
    Cvc5_external.solver_get_proof solver (ProofComponent.to_cpp component)

  let proof_to_string ?(format = ProofFormat.Default) solver proof =
    Cvc5_external.solver_proof_to_string solver proof
      (ProofFormat.to_cpp format)

  let get_learned_literals ?(kind = LearnedLitType.Input) solver =
    Cvc5_external.solver_get_learned_literals solver
      (LearnedLitType.to_cpp kind)

  let get_model = Cvc5_external.solver_get_model

  let declare_sort ?(fresh = true) solver symbol arity =
    Cvc5_external.solver_declare_sort solver symbol arity fresh

  let declare_datatype = Cvc5_external.solver_declare_datatype

  let declare_fun = Cvc5_external.solver_declare_fun

  let define_fun = Cvc5_external.solver_define_fun

  let define_fun_rec ?(global = false) solver symbol vars sort body =
    Cvc5_external.solver_define_fun_rec solver symbol vars sort body global

  let define_fun_rec_term ?(global = false) solver fn vars body =
    Cvc5_external.solver_define_fun_rec_term solver fn vars body global

  let define_funs_rec ?(global = false) solver funs bound_vars bodies =
    Cvc5_external.solver_define_funs_rec solver funs bound_vars bodies global

  let get_quantifier_elimination =
    Cvc5_external.solver_get_quantifier_elimination

  let get_quantifier_elimination_disjunct =
    Cvc5_external.solver_get_quantifier_elimination_disjunct

  let declare_sep_heap = Cvc5_external.solver_declare_sep_heap

  let get_value_sep_heap = Cvc5_external.solver_get_value_sep_heap

  let get_value_sep_nil = Cvc5_external.solver_get_value_sep_nil

  let declare_pool = Cvc5_external.solver_declare_pool

  let block_model ?(mode = BlockModelsMode.Literals) solver =
    Cvc5_external.solver_block_model solver (BlockModelsMode.to_cpp mode)

  let block_model_values = Cvc5_external.solver_block_model_values

  let get_instantiations = Cvc5_external.solver_get_instantiations

  let get_interpolant ?grammar solver conj =
    match grammar with
    | None -> Cvc5_external.solver_get_interpolant solver conj
    | Some g -> Cvc5_external.solver_get_interpolant_grammar solver conj g

  let get_interpolant_next = Cvc5_external.solver_get_interpolant_next

  let get_abduct ?grammar solver conj =
    match grammar with
    | None -> Cvc5_external.solver_get_abduct solver conj
    | Some g -> Cvc5_external.solver_get_abduct_grammar solver conj g

  let get_abduct_next = Cvc5_external.solver_get_abduct_next

  let mk_grammar = Cvc5_external.solver_mk_grammar

  let synth_fun (a : solver) (b : TermManager.tm) (c : string)
    (d : Term.term array) (e : Sort.sort) (grammar : Grammar.grammar option) =
    match grammar with
    | Some f -> Cvc5_external.solver_synth_fun_with_grammar a b c d e f
    | None -> Cvc5_external.solver_synth_fun_no_grammar a b c d e

  let declare_sygus_var = Cvc5_external.solver_declare_sygus_var

  let add_sygus_constraint = Cvc5_external.solver_add_sygus_constraint

  let get_sygus_constraints = Cvc5_external.solver_get_sygus_constraints

  let add_sygus_assume = Cvc5_external.solver_add_sygus_assume

  let get_sygus_assumptions = Cvc5_external.solver_get_sygus_assumptions

  let add_sygus_inv_constraint =
    Cvc5_external.solver_add_sygus_inv_constraint

  let check_synth = Cvc5_external.solver_check_synth

  let check_synth_next = Cvc5_external.solver_check_synth_next

  let get_synth_solution = Cvc5_external.solver_get_synth_solution

  let get_synth_solutions = Cvc5_external.solver_get_synth_solutions

  let find_synth ?grammar solver target =
    match grammar with
    | None ->
      Cvc5_external.solver_find_synth solver (FindSynthTarget.to_cpp target)
    | Some g ->
      Cvc5_external.solver_find_synth_grammar solver
        (FindSynthTarget.to_cpp target) g

  let get_statistics = Statistics.of_solver
end
