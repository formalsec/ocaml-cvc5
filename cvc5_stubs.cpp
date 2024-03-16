#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/callback.h>
#include <caml/custom.h>

#include <string.h>

#include <cvc5/cvc5.h>

#define CVC5_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC5_TRY_CATCH_END \
  }                            \
  catch (cvc5::CVC5ApiException &e) { caml_invalid_argument(e.getMessage().c_str()); }

#define Val_cvc5(v) (*((cvc5::Solver**)Data_custom_val(v)))
#define Val_term(v) (*((cvc5::Term**)Data_custom_val(v)))

static value Val_result(cvc5::Result * r) {
  return caml_copy_nativeint((intnat) r);
}

static cvc5::Result * Result_val(value v){
  return (cvc5::Result *) Nativeint_val(v);
}

static void internal_cvc5_delete (value vt)
{
  cvc5::Solver* solver = Val_cvc5(vt);
  Val_cvc5(vt) = nullptr;
  if (solver != nullptr) {
    delete solver;
  }
}

static void term_delete(value v){
  delete Val_term(v);
}

static struct custom_operations cvc5_operations =
{
   "https://cvc5.github.io/",
   internal_cvc5_delete,
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

extern "C" CAMLprim value ocaml_cvc5_stub_new_solver(){
  cvc5::Solver* solver = new cvc5::Solver();
  value v = caml_alloc_custom(&cvc5_operations, sizeof(cvc5::Solver*), 0, 1);
  Val_cvc5(v) = solver;
  return v;
}

extern "C" CAMLprim value ocaml_cvc5_stub_delete(value v){
  internal_cvc5_delete(v);
  return Val_unit;
}

extern "C" CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  CAMLparam0();
  CAMLlocal1(vt);
  cvc5::Solver* solver = Val_cvc5(v);
  CVC5_TRY_CATCH_BEGIN;
  cvc5::Term term = solver->mkTrue();
  value vt = caml_alloc_custom(&term_operations, sizeof(cvc5::Term*), 0, 1);
  Val_term(vt) = new cvc5::Term(term);
  CAMLreturn(vt);
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_assert_formula(value v, value t){
  cvc5::Solver* solver = Val_cvc5(v);
  cvc5::Term* term = Val_term(t);
  CVC5_TRY_CATCH_BEGIN;
  solver->assertFormula(*term);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

extern "C" CAMLprim value ocaml_cvc5_stub_check_sat(value v){
  cvc5::Solver* solver = Val_cvc5(v);
  cvc5::Result result = solver->checkSat();
  return Val_result(&result);
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_sat(value v){
  cvc5::Result* result = Result_val(v);
  return Val_bool(result->isSat());
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unsat(value v){
  cvc5::Result* result = Result_val(v);
  return Val_bool(result->isUnsat());
}

extern "C" CAMLprim value ocaml_cvc5_stub_result_is_unknown(value v){
  cvc5::Result* result = Result_val(v);
  return Val_bool(result->isUnknown());
}
