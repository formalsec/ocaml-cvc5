#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
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

#define Cvc5_val(v) (*((cvc5::Solver**)Data_custom_val(v)))
#define Term_val(v) (*((cvc5::Term**)Data_custom_val(v)))
#define TermManager_val(v) (*((cvc5::TermManager**)Data_custom_val(v)))
#define Result_val(v) (*((cvc5::Result**)Data_custom_val(v)))
#define Sort_val(v) (*((cvc5::Sort**)Data_custom_val(v)))

static void internal_cvc5_delete (value vt)
{
  cvc5::Solver* solver = Cvc5_val(vt);
  Cvc5_val(vt) = nullptr;
  if (solver != nullptr) {
    delete solver;
  }
}

static void term_delete(value v){
  cvc5::Term* term = Term_val(v);
  Term_val(v) = nullptr;
  if (term != nullptr)
    delete Term_val(v);
}

static void term_manager_delete(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  TermManager_val(v) = nullptr;
  if (term_manager != nullptr)
    delete TermManager_val(v);
}

static void result_delete(value v){
  cvc5::Result* result = Result_val(v);
  Result_val(v) = nullptr;
  if (result != nullptr)
    delete Result_val(v);
}

static void sort_delete(value v){
  cvc5::Sort* sort = Sort_val(v);
  Sort_val(v) = nullptr;
  if (sort != nullptr)
    delete Sort_val(v);
}

static struct custom_operations cvc5_operations =
{
   "https://cvc5.github.io/",
   &internal_cvc5_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

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

extern "C" CAMLprim value ocaml_cvc5_stub_new_solver(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Solver* solver = new cvc5::Solver(*term_manager);
  value r = caml_alloc_custom(&cvc5_operations, sizeof(cvc5::Solver*), 0, 1);
  Cvc5_val(r) = solver;
  return r;
}

extern "C" CAMLprim value ocaml_cvc5_stub_delete(value v){
  internal_cvc5_delete(v);
  return Val_unit;
}

extern "C" CAMLprim value ocaml_cvc5_stub_new_term_manager(){
  cvc5::TermManager* term_manager = new cvc5::TermManager();
  value v = caml_alloc_custom(&term_manager_operations, sizeof(cvc5::TermManager*), 0, 1);
  TermManager_val(v) = term_manager;
  return v;
}

extern "C" CAMLprim value ocaml_cvc5_stub_delete_term_manager(value v){
  term_manager_delete(v);
  return Val_unit;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkTrue());
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_false(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkFalse());
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_bool(value v, value b){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkBoolean(Bool_val(b)));
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_int(value v, value i){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkInteger(Int_val(i)));
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_real(value v, value r){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkReal(String_val(r)));
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_term_to_string(value v){
  return caml_copy_string(Term_val(v)->toString().c_str());
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_string(value v, value s){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkString(String_val(s)));
  return vt;
  CVC5_TRY_CATCH_END;
}

class Sort : public cvc5::Sort {
public:
  Sort(cvc5::Sort t) : cvc5::Sort(t) {}
  ~Sort() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Sort_val(*custom);
  }
};

extern "C" CAMLprim value ocaml_cvc5_stub_get_boolean_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(term_manager->getBooleanSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_get_integer_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&sort_operations, sizeof(cvc5::Sort*), 0, 1);
  Sort_val(vt) = new cvc5::Sort(term_manager->getIntegerSort());
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_const(value v, value sort, value n){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Sort* s = Sort_val(sort);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Term_val(vt) = new cvc5::Term(term_manager->mkConst(*s, String_val(n)));
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_assert_formula(value v, value t){
  CVC5_TRY_CATCH_BEGIN;
  Cvc5_val(v)->assertFormula(*Term_val(t));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_check_sat(value v){
  cvc5::Solver* solver = Cvc5_val(v);
  cvc5::Result result = solver->checkSat();
  value vt = caml_alloc_custom(&result_operations, sizeof(cvc5::Result*), 0, 1);
  Result_val(vt) = new cvc5::Result(result);
  return vt;
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_sat(value v){
  return Val_bool(Result_val(v)->isSat());
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unsat(value v){
  return Val_bool(Result_val(v)->isUnsat());
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unknown(value v){
  return Val_bool(Result_val(v)->isUnknown());
}