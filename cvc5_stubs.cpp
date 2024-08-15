/**************************************************************************
 *  Copyright (C) 2024 formalsec                                          *
 *                                                                        *
 *  This file is part of ocaml-cvc5                                       *
 *                                                                        *
 *  ocaml-cvc5 is free software: you can redistribute it and/or modify    *
 *  it under the terms of the GNU General Public License as published     *
 *  by the Free Software Foundation, either version 3 of the License,     *
 *  or (at your option) any later version.                                *
 *                                                                        *
 *  ocaml-cvc5 is distributed in the hope that it will be useful,         *
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of        *
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *
 *  See the GNU General Public License for more details.                  *
 *                                                                        *
 *  You should have received a copy of the GNU General Public License     *
 *  along with ocaml-cvc5. If not, see <http://www.gnu.org/licenses/>.    *
 **************************************************************************/

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/custom.h>
#include <atomic>
#include <string.h>
#include <iostream>
#include <algorithm>
#include <tuple>

#include <cvc5/cvc5.h>

#define CVC5_TRY_CATCH_BEGIN \
  try                            \
  {
#define CVC5_TRY_CATCH_END \
  }                            \
  catch (cvc5::CVC5ApiException &e) { caml_invalid_argument(e.getMessage().c_str()); }

extern "C"
{

int compare_ptrs(void* pt1, void* pt2) {
  if (pt1 == pt2)
    return 0;
  else if ((intnat)pt1 < (intnat)pt2)
    return -1;
  else
    return +1;
}

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
  /* Used for API-level reference counting */
  std::atomic<unsigned long> rc;
  TermManager() : cvc5::TermManager() { rc = 1; }
  ~TermManager() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
  void addRef() { rc.fetch_add(1, std::memory_order_release); }
};

#define TermManager_val(v) ((TermManager*)Data_custom_val(v))

int cvc5_tm_compare(value v1, value v2){
  TermManager* tm1 = TermManager_val(v1);
  TermManager* tm2 = TermManager_val(v2);
  return compare_ptrs(tm1, tm2);
}

intnat cvc5_tm_hash(value v){
  TermManager* tm = TermManager_val(v);
  return (intnat)tm;
}

static void try_delete_tm(TermManager* tm){
  if (tm->rc == 0) { delete tm; }
}

static void delete_tm(value v){
  TermManager* tm = TermManager_val(v);
  tm->rc--;
  try_delete_tm(tm);
}

static struct custom_operations term_manager_operations =
{
   "https://cvc5.github.io/",
   &delete_tm,
   cvc5_tm_compare,
   cvc5_tm_hash,
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
  TermManager* _tm;
  Term(cvc5::Term t, TermManager* tm) : cvc5::Term(t) {
    if (tm != NULL) { _tm = tm; tm->addRef(); }
    else { _tm = NULL; }
  }
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
  Term* term = Term_val(v);
  if (term->_tm != NULL) {
    // decrement the reference count of the term manager
    term->_tm->rc--;
    try_delete_tm(term->_tm);
  }
  delete term;
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
  TermManager* _tm;
  Sort(cvc5::Sort t, TermManager* tm) : cvc5::Sort(t) {
    if (tm != NULL) { _tm = tm; tm->addRef(); }
    else { _tm = NULL; }
  }
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
  Sort* sort = Sort_val(v);
  if (sort->_tm != NULL) {
    // decrement the reference count of the term manager
    sort->_tm->rc--;
    try_delete_tm(sort->_tm);
  }
  delete sort;
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
 *                              Op
 ============================================================================*/

class Op : public cvc5::Op {
public:
  Op(cvc5::Op t) : cvc5::Op(t) {}
  ~Op() {}
  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define OP_val(v) ((Op*)Data_custom_val(v))

static void op_delete(value v){
  delete OP_val(v);
}

static struct custom_operations op_operations =
{
   "https://cvc5.github.io/",
   &op_delete,
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
  CAMLparam1(v);
  CAMLlocal1(r);
  TermManager* tm = TermManager_val(v);
  cvc5::Solver* solver = new cvc5::Solver(*tm);
  r = caml_alloc_custom(&solver_operations, sizeof(cvc5::Solver*), 0, 1);
  Solver_val(r) = solver;
  CAMLreturn(r);
}

CAMLprim value ocaml_cvc5_stub_delete(value v){
  CVC5_TRY_CATCH_BEGIN;
  solver_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_new_term_manager(){
  CAMLparam0();
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_manager_operations, &custom) TermManager();
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_term_manager(value v){
  CVC5_TRY_CATCH_BEGIN;
  delete_tm(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_term(value v){
  CVC5_TRY_CATCH_BEGIN;
  term_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_sort(value v){
  CVC5_TRY_CATCH_BEGIN;
  sort_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_result(value v){
  CVC5_TRY_CATCH_BEGIN;
  result_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_equal(value t1, value t2){
  return Val_bool(*Term_val(t1) == *Term_val(t2));
}

CAMLprim value ocaml_cvc5_stub_sort_equal(value s1, value s2){
  return Val_bool(*Sort_val(s1) == *Sort_val(s2));
}

CAMLprim value ocaml_cvc5_stub_result_equal(value r1, value r2){
  return Val_bool(*Result_val(r1) == *Result_val(r2));
}

CAMLprim value ocaml_cvc5_stub_term_id(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Term_val(v)->getId());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_kind(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Term_val(v)->getKind());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(Term_val(v)->getSort(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkTrue(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_false(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkFalse(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bool(value v, value b){
  CAMLparam2(v, b);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkBoolean(Bool_val(b)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_int(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkInteger(Int_val(i)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real_s(value v, value r){
  CAMLparam2(v, r);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkReal(String_val(r)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_real_i(value v, int64_t i){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkReal(i), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real_i(value v, value i){
  return native_cvc5_stub_mk_real_i(v, Int64_val(i));
}

CAMLprim value native_cvc5_stub_mk_real(value v, int64_t num, int64_t den){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkReal(num, den), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real(value v, value num, value den){
  return native_cvc5_stub_mk_real(v, Int64_val(num), Int64_val(den));
}

CAMLprim value native_cvc5_stub_mk_bv(value v, uint32_t size, int64_t i){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkBitVector(size, i), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv(value v, value size, value i){
  return native_cvc5_stub_mk_bv(v, Long_val(size), Int64_val(i));
}

CAMLprim value native_cvc5_stub_mk_bv_s(value v, uint32_t size, value s, uint32_t base){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkBitVector(size, String_val(s), base), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv_s(value v, value size, value s, value base){
  return native_cvc5_stub_mk_bv_s(v, Long_val(size), s, Long_val(base));
}

CAMLprim value ocaml_cvc5_stub_term_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Term_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_string(value v, value s, value b){
  CAMLparam3(v, s, b);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(tm->mkString(String_val(s), Bool_val(b)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term(value v, value kind, value t){
  CAMLparam3(v, kind, t);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom)
    Term(tm->mkTerm((cvc5::Kind)Int_val(kind), args), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_1(value v, value kind, value t){
  CAMLparam3(v, kind, t);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t)};
  new(&term_operations, &custom)
    Term(tm->mkTerm((cvc5::Kind)Int_val(kind), args), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_2(value v, value kind, value t1, value t2){
  CAMLparam4(v, kind, t1, t2);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t1), *Term_val(t2)};
  new(&term_operations, &custom)
    Term(tm->mkTerm((cvc5::Kind)Int_val(kind), args), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_3(value v, value kind, value t1, value t2, value t3){
  CAMLparam5(v, kind, t1, t2, t3);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t1), *Term_val(t2), *Term_val(t3)};
  new(&term_operations, &custom)
    Term(tm->mkTerm((cvc5::Kind)Int_val(kind), args), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_with_op(value v, value op, value t){
  CAMLparam3(v, op, t);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom)
    Term(tm->mkTerm(*OP_val(op), args), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_fun(value slv, value symbol, value sorts, value r) {
  CAMLparam4(slv, symbol, sorts, r);
  CAMLlocal1(custom);
  cvc5::Solver* solver = Solver_val(slv);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec;
  size_t arity = Wosize_val(sorts);
  sort_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    sort_vec.emplace_back(*Sort_val(Field(sorts, i)));

  new(&term_operations, &custom)
    Term(solver->declareFun(String_val(symbol), sort_vec, *Sort_val(r)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_var_s(value v, value s, value n){
  CAMLparam3(v, s, n);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  cvc5::Sort* sort = Sort_val(s);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkVar(*sort, String_val(n)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_var(value v, value s){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  cvc5::Sort* sort = Sort_val(s);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkVar(*sort), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value
ocaml_cvc5_stub_define_fun(value slv, value symbol, value vars, value s, value body){
  CAMLparam5(slv, symbol, vars, s, body);
  CAMLlocal1(custom);
  cvc5::Solver* solver = Solver_val(slv);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> var_vec;
  size_t arity = Wosize_val(vars);
  var_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    var_vec.emplace_back(*Term_val(Field(vars, i)));

  new(&term_operations, &custom)
    Term(solver->defineFun(String_val(symbol), var_vec, *Sort_val(s), *Term_val(body)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_int_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Term_val(t)->getIntegerValue().c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_int_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Term_val(t)->isIntegerValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_real_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Term_val(t)->getRealValue().c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_real_value(value t){
  return Val_bool(Term_val(t)->isRealValue());
}

CAMLprim value ocaml_cvc5_stub_is_string_value(value t){
  return Val_bool(Term_val(t)->isStringValue());
}

CAMLprim value ocaml_cvc5_stub_get_string_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  std::wstring ws = Term_val(t)->getStringValue();
  std::string to_return;
  std::transform(ws.begin(), ws.end(), std::back_inserter(to_return), [] (wchar_t c) {
    return (char)c;
  });
  return caml_copy_string(to_return.c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_int32_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_int32(Term_val(t)->getInt32Value());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_int32_value(value t){
  return Val_bool(Term_val(t)->isInt32Value());
}

CAMLprim value ocaml_cvc5_stub_get_int64_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_int64(Term_val(t)->getInt64Value());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_int64_value(value t){
  return Val_bool(Term_val(t)->isInt64Value());
}

CAMLprim value ocaml_cvc5_stub_get_uint32_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Term_val(t)->getUInt32Value());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_uint32_value(value t){
  return Val_bool(Term_val(t)->isUInt32Value());
}

CAMLprim value ocaml_cvc5_stub_get_uint64_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_int64(Term_val(t)->getUInt64Value());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_uint64_value(value t){
  return Val_bool(Term_val(t)->isUInt64Value());
}

CAMLprim value native_cvc5_stub_get_bv_value(value t, uint32_t base){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Term_val(t)->getBitVectorValue(base).c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_bv_value(value t, value base){
  return native_cvc5_stub_get_bv_value(t, Long_val(base));
}

CAMLprim value ocaml_cvc5_stub_is_bv_value(value t){
  return Val_bool(Term_val(t)->isBitVectorValue());
}

CAMLprim value ocaml_cvc5_stub_get_rm_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int((int)(Term_val(t)->getRoundingModeValue()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_rm_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Term_val(t)->isRoundingModeValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_fp_value(value t) {
  CAMLparam1(t);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Term_val(t)->isFloatingPointValue()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_fp_value(value t) {
  CAMLparam1(t);
  CAMLlocal2(custom, term);
  TermManager *tm = TermManager_val(t);
  const auto fp = Term_val(t)->getFloatingPointValue();
  int ebits = std::get<0>(fp);
  int sbits = std::get<1>(fp);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &term) Term(std::get<2>(fp), tm);
  custom = caml_alloc_tuple(3);
  Store_field (custom, 0, Val_int(ebits));
  Store_field (custom, 1, Val_int(sbits));
  Store_field (custom, 2, term);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_bool_value(value t){
  CAMLparam1(t);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Term_val(t)->isBooleanValue()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_bool_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Term_val(t)->getBooleanValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_rounding_mode(value v, value rm){
  CAMLparam2(v, rm);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkRoundingMode((cvc5::RoundingMode)Int_val(rm)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_boolean_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->getBooleanSort(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_integer_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->getIntegerSort(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bitvector_sort(value v, value size){
  CAMLparam2(v, size);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->mkBitVectorSort(Int_val(size)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_real_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->getRealSort(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_string_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->getStringSort(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_rm_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->getRoundingModeSort(), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_get_bv_size(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Sort_val(v)->getBitVectorSize());
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_fp_sort(value v, uint32_t exp, uint32_t sig){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->mkFloatingPointSort(exp, sig), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_sort(value v, value exp, value sig){
  return native_cvc5_stub_mk_fp_sort(v, Long_val(exp), Long_val(sig));
}

CAMLprim value ocaml_cvc5_stub_mk_seq_sort(value v, value sort){
  CAMLparam2(v, sort);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->mkSequenceSort(*Sort_val(sort)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_uninterpreted_sort(value v, value s){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(tm->mkUninterpretedSort(String_val(s)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Sort_val(v)->toString().c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_const_s(value v, value sort, value n){
  CAMLparam3(v, sort, n);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  cvc5::Sort* s = Sort_val(sort);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkConst(*s, String_val(n)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_const(value v, value sort){
  CAMLparam2(v, sort);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  cvc5::Sort* s = Sort_val(sort);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkConst(*s), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_assert_formula(value v, value t){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->assertFormula(*Term_val(t));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_check_sat(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  cvc5::Solver* solver = Solver_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&result_operations, &custom)
    Result(solver->checkSat());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_check_sat_assuming(value v, value t){
  CAMLparam2(v, t);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> assumptions;
  size_t arity = Wosize_val(t);
  assumptions.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    assumptions.emplace_back(*Term_val(Field(t, i)));

  new(&result_operations, &custom)
    Result(Solver_val(v)->checkSatAssuming(assumptions));
  CAMLreturn(custom);
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

CAMLprim value ocaml_cvc5_stub_result_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Result_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_set_logic(value v, value s){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(v)->setLogic(String_val(s));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_set_option(value s, value opt, value v){
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(s)->setOption(String_val(opt), String_val(v));
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_simplify(value v, value t){
  CAMLparam2(v, t);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(v)->simplify(*Term_val(t)), NULL);
  CAMLreturn(custom);
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

CAMLprim value ocaml_cvc5_stub_solver_get_value(value v, value t){
  CAMLparam2(v, t);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(v)->getValue(*Term_val(t)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_values(value v, value ts){
  CAMLparam2(v, ts);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms;
  size_t arity = Wosize_val(ts);
  terms.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    terms.emplace_back(*Term_val(Field(ts, i)));

  std::vector<cvc5::Term> values = Solver_val(v)->getValue(terms);
  size_t n = values.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&term_manager_operations, &custom) Term(values[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_model_domain_elements(value v, value s){
  CAMLparam2(v, s);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> elements = Solver_val(v)->getModelDomainElements(*Sort_val(s));
  size_t n = elements.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(elements[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_unsat_core(value v){
  CAMLparam1(v);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> core = Solver_val(v)->getUnsatCore();
  size_t n = core.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(core[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_from_terms(value v, value sign, value exp, value sig){
  CAMLparam4(v, sign, exp, sig);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPoint(*Term_val(sign), *Term_val(exp), *Term_val(sig)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_fp(value v, uint32_t exp, uint32_t sig, value val){
  CAMLparam2(v, val);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPoint(exp, sig, *Term_val(val)), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp(value v, value sign, value exp, value sig){
  return native_cvc5_stub_mk_fp(v, Long_val(sign), Long_val(exp), sig);
}

CAMLprim value native_cvc5_stub_mk_fp_pos_inf(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPointPosInf(sign, exp), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_inf(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_inf(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPointNegInf(sign, exp), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_neg_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_neg_inf(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_nan(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPointNaN(sign, exp), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_nan(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_nan(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_pos_zero(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPointPosZero(sign, exp), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_zero(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_zero(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_zero(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(tm->mkFloatingPointNegZero(sign, exp), tm);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_neg_zero(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_neg_zero(v, Long_val(sign), Long_val(exp));
}

CAMLprim value ocaml_cvc5_stub_get_model(value v, value sorts, value vars){
  CAMLparam3(v, sorts, vars);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec;
  std::vector<cvc5::Term> term_vec;
  size_t arity = Wosize_val(sorts);
  sort_vec.reserve(arity);
  term_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    sort_vec.emplace_back(*Sort_val(Field(sorts, i)));

  for (size_t i = 0; i < arity; i++)
    term_vec.emplace_back(*Term_val(Field(vars, i)));

  CAMLreturn(caml_copy_string(Solver_val(v)->getModel(sort_vec, term_vec).c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_op(value v, value kind, value args){
  CAMLparam3(v, kind, args);
  CAMLlocal1(custom);
  TermManager* tm = TermManager_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<uint32_t> term_vec;
  size_t arity = Wosize_val(args);
  term_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    term_vec.emplace_back(Int_val(Field(args, i)));

  new(&op_operations, &custom)
    Op(tm->mkOp((cvc5::Kind)Int_val(kind), term_vec));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_op_equal(value o1, value o2){
  return Val_bool(*OP_val(o1) == *OP_val(o2));
}

CAMLprim value ocaml_cvc5_stub_op_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN
  CAMLreturn(caml_copy_string(OP_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_op_get_kind(value v){
  return Val_int(OP_val(v)->getKind());
}

CAMLprim value ocaml_cvc5_stub_op_get_num_indices(value v){
  return Val_int(OP_val(v)->getNumIndices());
}

CAMLprim value ocaml_cvc5_stub_op_get_index(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  cvc5::Op op = *OP_val(v);
  size_t index = Int_val(i);
  new(&term_operations, &custom)
    Term(op[index], NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_op_is_indexed(value v){
  return Val_bool(OP_val(v)->isIndexed());
}

CAMLprim intnat native_cvc5_stub_op_hash(value v){
  return std::hash<cvc5::Op>{}(*OP_val(v));
}

CAMLprim value ocaml_cvc5_stub_op_hash(value v){
  return Val_long(native_cvc5_stub_op_hash(v));
}

CAMLprim value ocaml_cvc5_stub_op_delete(value v){
  CVC5_TRY_CATCH_BEGIN;
  op_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

} // extern "C"
