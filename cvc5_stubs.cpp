#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/custom.h>

#include <string.h>
#include <iostream>

#include <cvc5/cvc5.h>

#define CVC5_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC5_TRY_CATCH_END \
  }                            \
  catch (cvc5::CVC5ApiException &e) { caml_invalid_argument(e.getMessage().c_str()); }

extern "C" 
{

/*============================================================================
 *                              Solver            
 ============================================================================*/

#define Solver_val(v) (*((cvc5::Solver**)Data_custom_val(v)))

static void solver_delete (value vt)
{
  cvc5::Solver* solver = Solver_val(vt);
  Solver_val(vt) = nullptr;
  if (solver != nullptr) {
    delete solver;
  }
}

static struct custom_operations solver_operations =
{
   "https://cvc5.github.io/",
   &solver_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Term Manager            
 ============================================================================*/

class TermManager : public cvc5::TermManager {
public:
  TermManager() : cvc5::TermManager() {}
  ~TermManager() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define TermManager_val(v) ((TermManager*)Data_custom_val(v))

static void term_manager_delete(value v){
  delete TermManager_val(v);
}


static struct custom_operations term_manager_operations =
{
   "https://cvc5.github.io/",
   &term_manager_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Term            
 ============================================================================*/

class Term : public cvc5::Term {
public:
  Term(cvc5::Term t) : cvc5::Term(t) {}
  ~Term() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define Term_val(v) ((Term*)Data_custom_val(v))

static void term_delete(value v){
  delete Term_val(v);
}

static struct custom_operations term_operations =
{
   "https://cvc5.github.io/",
   &term_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Sort            
 ============================================================================*/

class Sort : public cvc5::Sort {
public:
  Sort(cvc5::Sort t) : cvc5::Sort(t) {}
  ~Sort() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define Sort_val(v) ((Sort*)Data_custom_val(v))

static void sort_delete(value v){
  delete Sort_val(v);
}

static struct custom_operations sort_operations =
{
   "https://cvc5.github.io/",
   &sort_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Result            
 ============================================================================*/

class Result : public cvc5::Result {
public:
  Result(cvc5::Result t) : cvc5::Result(t) {}
  ~Result() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define Result_val(v) ((Result*)Data_custom_val(v))

static void result_delete(value v){
  delete Result_val(v);
}

static struct custom_operations result_operations =
{
   "https://cvc5.github.io/",
   &result_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Stubs            
 ============================================================================*/

CAMLprim value ocaml_cvc5_stub_new_solver(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Solver* solver = new cvc5::Solver(*term_manager);
  value r = caml_alloc_custom(&solver_operations, sizeof(cvc5::Solver*), 0, 1);
  Solver_val(r) = solver;
  return r;
}

CAMLprim value ocaml_cvc5_stub_delete(value v){
  CVC5_TRY_CATCH_BEGIN;
  solver_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_new_term_manager(){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_manager_operations, &custom) TermManager();
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_term_manager(value v){
  CVC5_TRY_CATCH_BEGIN;
  term_manager_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_equal(value t1, value t2){
  return Val_bool(*Term_val(t1) == *Term_val(t2));
}

CAMLprim value ocaml_cvc5_stub_term_id(value v){
  return Val_int(Term_val(v)->getId());
}

CAMLprim value ocaml_cvc5_stub_term_kind(value v){
  return Val_int(Term_val(v)->getKind());
}

CAMLprim value ocaml_cvc5_stub_term_sort(value v){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(Term_val(v)->getSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkTrue());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_false(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkFalse());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bool(value v, value b){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkBoolean(Bool_val(b)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_int(value v, value i){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkInteger(Int_val(i)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv(value v, value size, value i){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkBitVector(Int_val(size), Long_val(i)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real(value v, value r){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkReal(String_val(r)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_to_string(value v){
  return caml_copy_string(Term_val(v)->toString().c_str());
}

CAMLprim value ocaml_cvc5_stub_mk_string(value v, value s){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkString(String_val(s)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term(value v, value kind, value t){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom) 
    Term(term_manager->mkTerm((cvc5::Kind)Int_val(kind), args));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_rounding_mode(value v, value rm){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkRoundingMode((cvc5::RoundingMode)Int_val(rm)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_boolean_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->getBooleanSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_integer_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->getIntegerSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bitvector_sort(value v, value size){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->mkBitVectorSort(Int_val(size)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_real_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->getRealSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_string_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->getStringSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_const_s(value v, value sort, value n){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Sort* s = Sort_val(sort);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkConst(*s, String_val(n)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_const(value v, value sort){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Sort* s = Sort_val(sort);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkConst(*s));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_assert_formula(value v, value t){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->assertFormula(*Term_val(t));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_check_sat(value v){
  cvc5::Solver* solver = Solver_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&result_operations, &custom) 
    Result(solver->checkSat());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_result_is_sat(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Result_val(v)->isSat());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_result_is_unsat(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Result_val(v)->isUnsat());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_result_is_unknown(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Result_val(v)->isUnknown());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_set_logic(value v, value s){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->setLogic(String_val(s));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_simplify(value v, value t){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(Solver_val(v)->simplify(*Term_val(t)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_push(value v, value t){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->push(Int_val(t));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_pop(value v, value t){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->pop(Int_val(t));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_reset_assertions(value v){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->resetAssertions();
  return Val_unit;
  CVC5_TRY_CATCH_END;
}


} // extern "C"