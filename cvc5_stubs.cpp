/*------------------------------------------------------------------------*
 *  Copyright (C) 2024 formalsec                                       *
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
 *------------------------------------------------------------------------*/

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

CAMLprim value ocaml_cvc5_stub_mk_real_s(value v, value r){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkReal(String_val(r)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_real_i(value v, int64_t i){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkReal(i));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real_i(value v, value i){
  return native_cvc5_stub_mk_real_i(v, Int64_val(i));
}

CAMLprim value native_cvc5_stub_mk_real(value v, int64_t num, int64_t den){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkReal(num, den));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real(value v, value num, value den){
  return native_cvc5_stub_mk_real(v, Int64_val(num), Int64_val(den));
}

CAMLprim value native_cvc5_stub_mk_bv(value v, uint32_t size, uint64_t i){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkBitVector(size, i));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv(value v, value size, value i){
  return native_cvc5_stub_mk_bv(v, Int_val(size), Long_val(i));
}

CAMLprim value native_cvc5_stub_mk_bv_s(value v, uint32_t size, value s, uint32_t base){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkBitVector(size, String_val(s), base));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv_s(value v, value size, value s, value base){
  return native_cvc5_stub_mk_bv_s(v, Int_val(size), s, Int_val(base));
}

CAMLprim value ocaml_cvc5_stub_term_to_string(value v){
  return caml_copy_string(Term_val(v)->toString().c_str());
}

CAMLprim value ocaml_cvc5_stub_mk_string(value v, value s, value b){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(term_manager->mkString(String_val(s), Bool_val(b)));
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

CAMLprim value ocaml_cvc5_stub_mk_term_with_op(value v, value op, value t){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom) 
    Term(term_manager->mkTerm(*OP_val(op), args));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_fun(value slv, value symbol, value sorts, value r) {
  cvc5::Solver* solver = Solver_val(slv);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec;
  size_t arity = Wosize_val(sorts);
  sort_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    sort_vec.emplace_back(*Sort_val(Field(sorts, i)));

  new(&term_operations, &custom) 
    Term(solver->declareFun(String_val(symbol), sort_vec, *Sort_val(r)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_var_s(value v, value s, value n){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Sort* sort = Sort_val(s);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkVar(*sort, String_val(n)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_var(value v, value s){
  cvc5::TermManager* term_manager = TermManager_val(v);
  cvc5::Sort* sort = Sort_val(s);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkVar(*sort));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value 
ocaml_cvc5_stub_define_fun(value slv, value symbol, value vars, value s, value body){
  cvc5::Solver* solver = Solver_val(slv);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> var_vec;
  size_t arity = Wosize_val(vars);
  var_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    var_vec.emplace_back(*Term_val(Field(vars, i)));

  new(&term_operations, &custom) 
    Term(solver->defineFun(String_val(symbol), var_vec, *Sort_val(s), *Term_val(body)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_int_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Term_val(t)->getIntegerValue().c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_int_value(value t){
  return Val_bool(Term_val(t)->isIntegerValue());
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
  return caml_copy_string(Term_val(t)->getBitVectorValue(Int_val(base)).c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_bv_value(value t, value base){
  return native_cvc5_stub_get_bv_value(t, Int_val(base));
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
  return Val_bool(Term_val(t)->isRoundingModeValue());
}

CAMLprim value ocaml_cvc5_stub_is_bool_value(value t){
  return Val_bool(Term_val(t)->isBooleanValue());
}

CAMLprim value ocaml_cvc5_stub_get_bool_value(value t){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Term_val(t)->getBooleanValue());
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

CAMLprim value ocaml_cvc5_stub_get_rm_sort(value v){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->getRoundingModeSort());
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_get_bv_size(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Sort_val(v)->getBitVectorSize());
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_fp_sort(value v, uint32_t exp, uint32_t sig){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->mkFloatingPointSort(exp, sig));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_sort(value v, value exp, value sig){
  return native_cvc5_stub_mk_fp_sort(v, Int_val(exp), Int_val(sig));
}

CAMLprim value ocaml_cvc5_stub_mk_seq_sort(value v, value sort){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->mkSequenceSort(*Sort_val(sort)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_uninterpreted_sort(value v, value s){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) 
    Sort(term_manager->mkUninterpretedSort(String_val(s)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_to_string(value v){
  return caml_copy_string(Sort_val(v)->toString().c_str());
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

CAMLprim value ocaml_cvc5_stub_check_sat_assuming(value v, value t){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> assumptions;
  size_t arity = Wosize_val(t);
  assumptions.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    assumptions.emplace_back(*Term_val(Field(t, i)));

  new(&result_operations, &custom)
    Result(Solver_val(v)->checkSatAssuming(assumptions));
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

CAMLprim value ocaml_cvc5_stub_result_to_string(value v){
  return caml_copy_string(Result_val(v)->toString().c_str());
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

CAMLprim value ocaml_cvc5_stub_solver_get_value(value v, value t){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(Solver_val(v)->getValue(*Term_val(t)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_values(value v, value ts){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms;
  size_t arity = Wosize_val(ts);
  terms.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    terms.emplace_back(*Term_val(Field(ts, i)));

  std::vector<cvc5::Term> values = Solver_val(v)->getValue(terms);
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = values.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&sort_operations, &custom) Term(values[i]);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_model_domain_elements(value v, value s){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> elements = Solver_val(v)->getModelDomainElements(*Sort_val(s));
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = elements.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&sort_operations, &custom) Term(elements[i]);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_unsat_core(value v){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> core = Solver_val(v)->getUnsatCore();
  CAMLparam0();
  CAMLlocal1(result);
  size_t n = core.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; i += 1) {
    value custom = Val_unit;
    new(&sort_operations, &custom) Term(core[i]);
    caml_modify(&Field(result, i), custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_from_terms(value v, value sign, value exp, value sig){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPoint(*Term_val(sign), *Term_val(exp), *Term_val(sig)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_fp(value v, uint32_t exp, uint32_t sig, value val){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPoint(exp, sig, *Term_val(val)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp(value v, value sign, value exp, value sig){
  return native_cvc5_stub_mk_fp(v, Int_val(sign), Int_val(exp), sig);
}

CAMLprim value native_cvc5_stub_mk_fp_pos_inf(value v, uint32_t sign, uint32_t exp){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPointPosInf(Int_val(sign), Int_val(exp)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_inf(v, Int_val(sign), Int_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_inf(value v, uint32_t sign, uint32_t exp){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPointNegInf(Int_val(sign), Int_val(exp)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_neg_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_neg_inf(v, Int_val(sign), Int_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_nan(value v, uint32_t sign, uint32_t exp){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPointNaN(Int_val(sign), Int_val(exp)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_nan(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_nan(v, Int_val(sign), Int_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_pos_zero(value v, uint32_t sign, uint32_t exp){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPointPosZero(Int_val(sign), Int_val(exp)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_zero(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_zero(v, Int_val(sign), Int_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_zero(value v, uint32_t sign, uint32_t exp){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) 
    Term(term_manager->mkFloatingPointNegZero(Int_val(sign), Int_val(exp)));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_neg_zero(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_neg_zero(v, Int_val(sign), Int_val(exp));
}

CAMLprim value ocaml_cvc5_stub_get_model(value v, value sorts, value vars){
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

  return caml_copy_string(Solver_val(v)->getModel(sort_vec, term_vec).c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_op(value v, value kind, value args){
  cvc5::TermManager* term_manager = TermManager_val(v);
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  std::vector<uint32_t> term_vec;
  size_t arity = Wosize_val(args);
  term_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    term_vec.emplace_back(Int_val(Field(args, i)));

  new(&op_operations, &custom) 
    Op(term_manager->mkOp((cvc5::Kind)Int_val(kind), term_vec));
  return custom;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_op_equal(value o1, value o2){
  return Val_bool(*OP_val(o1) == *OP_val(o2));
}

CAMLprim value ocaml_cvc5_stub_op_to_string(value v){
  return caml_copy_string(OP_val(v)->toString().c_str());
}

CAMLprim value ocaml_cvc5_stub_op_get_kind(value v){
  return Val_int(OP_val(v)->getKind());
}

CAMLprim value ocaml_cvc5_stub_op_get_num_indices(value v){
  return Val_int(OP_val(v)->getNumIndices());
}

CAMLprim value ocaml_cvc5_stub_op_get_index(value v, value i){
  value custom = Val_unit;
  CVC5_TRY_CATCH_BEGIN;
  cvc5::Op op = *OP_val(v);
  size_t index = Int_val(i);
  new(&term_operations, &custom) 
    Term(op[index]);
  return custom;
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