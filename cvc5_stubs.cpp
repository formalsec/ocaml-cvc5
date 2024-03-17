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

#define Val_cvc5(v) (*((cvc5::Solver**)Data_custom_val(v)))
#define Val_term(v) (*((cvc5::Term**)Data_custom_val(v)))
#define Val_term_manager(v) (*((cvc5::TermManager**)Data_custom_val(v)))
#define Val_result(v) (*((cvc5::Result**)Data_custom_val(v)))

static void internal_cvc5_delete (value vt)
{
  cvc5::Solver* solver = Val_cvc5(vt);
  Val_cvc5(vt) = nullptr;
  if (solver != nullptr) {
    delete solver;
  }
}

static void term_delete(value v){
  cvc5::Term* term = Val_term(v);
  Val_term(v) = nullptr;
  if (term != nullptr)
    delete Val_term(v);
}

static void term_manager_delete(value v){
  cvc5::TermManager* term_manager = Val_term_manager(v);
  Val_term_manager(v) = nullptr;
  if (term_manager != nullptr)
    delete Val_term_manager(v);
}

static void result_delete(value v){
  cvc5::Result* result = Val_result(v);
  Val_result(v) = nullptr;
  if (result != nullptr)
    delete Val_result(v);
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

extern "C" CAMLprim value ocaml_cvc5_stub_new_solver(value v){
  cvc5::TermManager* term_manager = Val_term_manager(v);
  cvc5::Solver* solver = new cvc5::Solver(*term_manager);
  value r = caml_alloc_custom(&cvc5_operations, sizeof(cvc5::Solver*), 0, 1);
  Val_cvc5(r) = solver;
  return r;
}

extern "C" CAMLprim value ocaml_cvc5_stub_delete(value v){
  internal_cvc5_delete(v);
  return Val_unit;
}

extern "C" CAMLprim value ocaml_cvc5_stub_new_term_manager(){
  cvc5::TermManager* term_manager = new cvc5::TermManager();
  value v = caml_alloc_custom(&term_manager_operations, sizeof(cvc5::TermManager*), 0, 1);
  Val_term_manager(v) = term_manager;
  return v;
}

extern "C" CAMLprim value ocaml_cvc5_stub_delete_term_manager(value v){
  term_manager_delete(v);
  return Val_unit;
}

extern "C" CAMLprim value stub_foo(value v){
  cvc5::TermManager* term_manager = Val_term_manager(v);
  cvc5::Solver* solver = new cvc5::Solver(*term_manager);
  // cvc5::Term x = term_manager->mkTrue();
  //solver->assertFormula(*term);
  return Val_unit;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  cvc5::TermManager* term_manager = Val_term_manager(v);
  CVC5_TRY_CATCH_BEGIN;
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Val_term(vt) = new cvc5::Term(term_manager->mkTrue());
  return vt;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_assert_formula(value v, value t){
  // cvc5::Term* term = Val_term(t);
  CVC5_TRY_CATCH_BEGIN;
  Val_cvc5(v)->assertFormula(*Val_term(t));
  // cvc5::Result result = solver->checkSat();
  // std::cout << "result in c++: " << result.toString() << std::endl;
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_check_sat(value v){
  cvc5::Solver* solver = Val_cvc5(v);
  cvc5::Result result = solver->checkSat();
  value vt = caml_alloc_custom(&cvc5_operations, sizeof(cvc5::Result*), 0, 1);
  Val_result(vt) = new cvc5::Result(result);
  return vt;
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_sat(value v, value t){
  bool is_sat = Val_result(v)->isSat();
  std::cout << "is_sat: " << is_sat << std::endl;
  cvc5::TermManager* term_manager = Val_term_manager(t);
  cvc5::Term x = term_manager->mkTrue();
  std::cout << "x: " << x.toString() << std::endl;
  return Val_bool(is_sat);
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unsat(value v){
  return Val_bool(Val_result(v)->isUnsat());
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unknown(value v){
  return Val_bool(Val_result(v)->isUnknown());
}