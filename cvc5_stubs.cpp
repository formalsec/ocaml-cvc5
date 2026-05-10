/* SPDX-License-Identifier: MIT */ 
/* Copyright (C) 2024-2025 formalsec */
/* Written by Joao Pereira */

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

struct TermManagerHandle {
  cvc5::TermManager* tm;
  std::atomic<unsigned long> rc;
  std::unordered_map<std::string, cvc5::Term*> const_map;
};

#define TermManager_val(v) ((*(TermManagerHandle **)Data_custom_val(v))->tm)
#define TermManager_handle_val(v) (*(TermManagerHandle**)Data_custom_val(v))

int cvc5_tm_compare(value v1, value v2){
  cvc5::TermManager* tm1 = TermManager_val(v1);
  cvc5::TermManager* tm2 = TermManager_val(v2);
  return compare_ptrs(tm1, tm2);
}

intnat cvc5_tm_hash(value v){
  cvc5::TermManager* tm = TermManager_val(v);
  return (intnat)tm;
}

static void delete_tm(value v) {
  TermManagerHandle* handle = TermManager_handle_val(v);
  handle->rc.fetch_sub(1, std::memory_order_release);
  if (handle->rc == 0) {
    delete handle->tm;
    delete handle;
  }
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
  Term(cvc5::Term t, TermManagerHandle* handle)
      : cvc5::Term(t), manager(handle) {
    if(manager) manager->rc.fetch_add(1, std::memory_order_release);
  }
  ~Term() { }

  void* operator new(size_t size, struct custom_operations *ops, value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }

  void operator delete(void* ptr) {}

  TermManagerHandle* getManager() const { return manager; }
private:
  TermManagerHandle* manager;
};

#define Term_val(v) ((Term*)Data_custom_val(v))


static void term_delete(value v) {
  Term* term = Term_val(v);
  if (term == nullptr) return;
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
 *                              Grammar
 ============================================================================*/

class Grammar : public cvc5::Grammar {
public:
  Grammar(cvc5::Grammar t) : cvc5::Grammar(t) {}

  ~Grammar() {}

  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define Grammar_val(v) ((Grammar*)Data_custom_val(v))

static void grammar_delete(value v){
  delete Grammar_val(v);
}

static struct custom_operations grammar_operations =
{
  "https://cvc5.github.io/",
  &grammar_delete,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default,
  custom_compare_ext_default,
  custom_fixed_length_default
};


/*============================================================================
 *                             SynthResult
 ============================================================================*/

class SynthResult : public cvc5::SynthResult {
public:
  SynthResult(cvc5::SynthResult t) : cvc5::SynthResult(t) {}
  ~SynthResult() {}

  void * operator new(size_t size,
        struct custom_operations *ops,
        value *custom){
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void *ptr) {}
};

#define Synthresult_val(v) ((SynthResult*)Data_custom_val(v))

static void synth_delete(value v) {
  delete Synthresult_val(v);
}

static struct custom_operations synthresult_operations =
{
  "https://cvc5.github.io/",
  &synth_delete,
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
  Sort(cvc5::Sort t) : cvc5::Sort(t) { }
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
  if (sort == nullptr) return;
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
 *                              Datatypes
 ============================================================================*/

class DatatypeConstructorDecl : public cvc5::DatatypeConstructorDecl {
public:
  DatatypeConstructorDecl(cvc5::DatatypeConstructorDecl t)
      : cvc5::DatatypeConstructorDecl(t) {}
  ~DatatypeConstructorDecl() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define DatatypeConstructorDecl_val(v) ((DatatypeConstructorDecl*)Data_custom_val(v))

static void datatype_constructor_decl_delete(value v) {
  delete DatatypeConstructorDecl_val(v);
}

static struct custom_operations datatype_constructor_decl_operations =
{
   "https://cvc5.github.io/",
   &datatype_constructor_decl_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class DatatypeDecl : public cvc5::DatatypeDecl {
public:
  DatatypeDecl(cvc5::DatatypeDecl t) : cvc5::DatatypeDecl(t) {}
  ~DatatypeDecl() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define DatatypeDecl_val(v) ((DatatypeDecl*)Data_custom_val(v))

static void datatype_decl_delete(value v) { delete DatatypeDecl_val(v); }

static struct custom_operations datatype_decl_operations =
{
   "https://cvc5.github.io/",
   &datatype_decl_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class DatatypeSelector : public cvc5::DatatypeSelector {
public:
  DatatypeSelector(cvc5::DatatypeSelector t) : cvc5::DatatypeSelector(t) {}
  ~DatatypeSelector() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define DatatypeSelector_val(v) ((DatatypeSelector*)Data_custom_val(v))

static void datatype_selector_delete(value v) { delete DatatypeSelector_val(v); }

static struct custom_operations datatype_selector_operations =
{
   "https://cvc5.github.io/",
   &datatype_selector_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class DatatypeConstructor : public cvc5::DatatypeConstructor {
public:
  DatatypeConstructor(cvc5::DatatypeConstructor t)
      : cvc5::DatatypeConstructor(t) {}
  ~DatatypeConstructor() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define DatatypeConstructor_val(v) ((DatatypeConstructor*)Data_custom_val(v))

static void datatype_constructor_delete(value v) {
  delete DatatypeConstructor_val(v);
}

static struct custom_operations datatype_constructor_operations =
{
   "https://cvc5.github.io/",
   &datatype_constructor_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class Datatype : public cvc5::Datatype {
public:
  Datatype(cvc5::Datatype t) : cvc5::Datatype(t) {}
  ~Datatype() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define Datatype_val(v) ((Datatype*)Data_custom_val(v))

static void datatype_delete(value v) { delete Datatype_val(v); }

static struct custom_operations datatype_operations =
{
   "https://cvc5.github.io/",
   &datatype_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

/*============================================================================
 *                              Proof / Options / Stats
 ============================================================================*/

class Proof : public cvc5::Proof {
public:
  Proof(cvc5::Proof t) : cvc5::Proof(t) {}
  ~Proof() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define Proof_val(v) ((Proof*)Data_custom_val(v))

static void proof_delete(value v) { delete Proof_val(v); }

static struct custom_operations proof_operations =
{
   "https://cvc5.github.io/",
   &proof_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

struct OptionInfo {
  cvc5::OptionInfo* info;
};

#define OptionInfo_val(v) (((OptionInfo*)Data_custom_val(v))->info)

static void option_info_delete(value v) {
  cvc5::OptionInfo* info = OptionInfo_val(v);
  ((OptionInfo*)Data_custom_val(v))->info = nullptr;
  delete info;
}

static struct custom_operations option_info_operations =
{
   "https://cvc5.github.io/",
   &option_info_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class Stat : public cvc5::Stat {
public:
  Stat(cvc5::Stat t) : cvc5::Stat(t) {}
  ~Stat() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define Stat_val(v) ((Stat*)Data_custom_val(v))

static void stat_delete(value v) { delete Stat_val(v); }

static struct custom_operations stat_operations =
{
   "https://cvc5.github.io/",
   &stat_delete,
   custom_compare_default,
   custom_hash_default,
   custom_serialize_default,
   custom_deserialize_default,
   custom_compare_ext_default,
   custom_fixed_length_default
};

class Statistics : public cvc5::Statistics {
public:
  Statistics(cvc5::Statistics t) : cvc5::Statistics(t) {}
  ~Statistics() {}
  void* operator new(size_t size, struct custom_operations* ops, value* custom) {
    *custom = caml_alloc_custom(ops, size, 0, 1);
    return Data_custom_val(*custom);
  }
  void operator delete(void* ptr) {}
};

#define Statistics_val(v) ((Statistics*)Data_custom_val(v))

static void statistics_delete(value v) { delete Statistics_val(v); }

static struct custom_operations statistics_operations =
{
   "https://cvc5.github.io/",
   &statistics_delete,
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

#define DEFINE_SORT_BOOL_STUB(name, method) \
  CAMLprim value name(value v){ \
    CVC5_TRY_CATCH_BEGIN; \
    return Val_bool(Sort_val(v)->method()); \
    CVC5_TRY_CATCH_END; \
  }

#define DEFINE_TERM_BOOL_STUB(name, method) \
  CAMLprim value name(value v){ \
    CVC5_TRY_CATCH_BEGIN; \
    return Val_bool(Term_val(v)->method()); \
    CVC5_TRY_CATCH_END; \
  }

#define DEFINE_TERM_UNARY_STUB(name, method) \
  CAMLprim value name(value v){ \
    CAMLparam1(v); \
    CAMLlocal1(custom); \
    CVC5_TRY_CATCH_BEGIN; \
    new(&term_operations, &custom) Term(Term_val(v)->method(), Term_val(v)->getManager()); \
    CAMLreturn(custom); \
    CVC5_TRY_CATCH_END; \
  }

#define DEFINE_TERM_BINARY_STUB(name, method) \
  CAMLprim value name(value v1, value v2){ \
    CAMLparam2(v1, v2); \
    CAMLlocal1(custom); \
    CVC5_TRY_CATCH_BEGIN; \
    new(&term_operations, &custom) Term(Term_val(v1)->method(*Term_val(v2)), Term_val(v1)->getManager()); \
    CAMLreturn(custom); \
    CVC5_TRY_CATCH_END; \
  }

CAMLprim value ocaml_cvc5_stub_new_solver(value v){
  CAMLparam1(v);
  CAMLlocal1(r);
  cvc5::Solver* solver = new cvc5::Solver(*TermManager_val(v));
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
  TermManagerHandle* handle = new TermManagerHandle {
    new cvc5::TermManager(),
    1
  };

  value vt = caml_alloc_custom(&term_manager_operations,
             sizeof(TermManagerHandle*), 0, 1);
  *(TermManagerHandle**)Data_custom_val(vt) = handle;
  return vt;
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
    Sort(Term_val(v)->getSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_true(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkTrue(), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_false(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkFalse(), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bool(value v, value b){
  CAMLparam2(v, b);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkBoolean(Bool_val(b)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_int(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkInteger(Int_val(i)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real_s(value v, value r){
  CAMLparam2(v, r);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkReal(String_val(r)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_real_i(value v, int64_t i){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkReal(i), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real_i(value v, value i){
  return native_cvc5_stub_mk_real_i(v, Int64_val(i));
}

CAMLprim value native_cvc5_stub_mk_real(value v, int64_t num, int64_t den){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkReal(num, den), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_real(value v, value num, value den){
  return native_cvc5_stub_mk_real(v, Int64_val(num), Int64_val(den));
}

CAMLprim value native_cvc5_stub_mk_bv(value v, uint32_t size, int64_t i){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkBitVector(size, i), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bv(value v, value size, value i){
  return native_cvc5_stub_mk_bv(v, Long_val(size), Int64_val(i));
}

CAMLprim value native_cvc5_stub_mk_bv_s(value v, uint32_t size, value s, uint32_t base){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkBitVector(size, String_val(s), base), handle);
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
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(handle->tm->mkString(String_val(s), Bool_val(b)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term(value v, value kind, value t){
  CAMLparam3(v, kind, t);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom)
    Term(handle->tm->mkTerm((cvc5::Kind)Int_val(kind), args), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_1(value v, value kind, value t){
  CAMLparam3(v, kind, t);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t)};
  new(&term_operations, &custom)
    Term(handle->tm->mkTerm((cvc5::Kind)Int_val(kind), args), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_2(value v, value kind, value t1, value t2){
  CAMLparam4(v, kind, t1, t2);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t1), *Term_val(t2)};
  new(&term_operations, &custom)
    Term(handle->tm->mkTerm((cvc5::Kind)Int_val(kind), args), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_3(value v, value kind, value t1, value t2, value t3){
  CAMLparam5(v, kind, t1, t2, t3);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = {*Term_val(t1), *Term_val(t2), *Term_val(t3)};
  new(&term_operations, &custom)
    Term(handle->tm->mkTerm((cvc5::Kind)Int_val(kind), args), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_term_with_op(value v, value op, value t){
  CAMLparam3(v, op, t);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args;
  size_t arity = Wosize_val(t);
  args.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    args.emplace_back(*Term_val(Field(t, i)));

  new(&term_operations, &custom)
    Term(handle->tm->mkTerm(*OP_val(op), args), handle);
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
  TermManagerHandle* handle = TermManager_handle_val(v);
  cvc5::Sort* sort = Sort_val(s);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkVar(*sort, String_val(n)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_var(value v, value s){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  cvc5::Sort* sort = Sort_val(s);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkVar(*sort), handle);
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
  std::u32string ws = Term_val(t)->getU32StringValue();
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
  TermManagerHandle* handle = TermManager_handle_val(t);
  const auto fp = Term_val(t)->getFloatingPointValue();
  int ebits = std::get<0>(fp);
  int sbits = std::get<1>(fp);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &term) Term(std::get<2>(fp), handle);
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
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkRoundingMode((cvc5::RoundingMode)Int_val(rm)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_boolean_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getBooleanSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_integer_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getIntegerSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_bitvector_sort(value v, value size){
  CAMLparam2(v, size);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->mkBitVectorSort(Int_val(size)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_real_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getRealSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_string_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getStringSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_regexp_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getRegExpSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_rm_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->getRoundingModeSort());
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
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->mkFloatingPointSort(exp, sig));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_sort(value v, value exp, value sig){
  return native_cvc5_stub_mk_fp_sort(v, Long_val(exp), Long_val(sig));
}

CAMLprim value ocaml_cvc5_stub_mk_seq_sort(value v, value sort){
  CAMLparam2(v, sort);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->mkSequenceSort(*Sort_val(sort)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_uninterpreted_sort(value v, value s){
  CAMLparam2(v, s);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(v)->mkUninterpretedSort(String_val(s)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_to_string(value v){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_string(Sort_val(v)->toString().c_str());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_const_s(value v, value sort, value n) {
  CAMLparam3(v, sort, n);
  CAMLlocal1(custom);

  TermManagerHandle* handle = TermManager_handle_val(v);
  cvc5::Sort* s = Sort_val(sort);
  std::string termName = String_val(n);
  auto it = handle->const_map.find(termName);
  if(it != handle->const_map.end()) {
    new(&term_operations, &custom) Term(*(it->second), handle);
    CAMLreturn(custom);
  }
  else {
    CVC5_TRY_CATCH_BEGIN;
    cvc5::Term* newTerm = new cvc5::Term(TermManager_val(v)->mkConst(*s, termName));
    handle->const_map.emplace(termName, newTerm);
    new(&term_operations, &custom) Term(*newTerm, handle);
    CAMLreturn(custom);
    CVC5_TRY_CATCH_END;
  }
}

CAMLprim value ocaml_cvc5_stub_mk_const(value v, value sort){
  CAMLparam2(v, sort);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  cvc5::Sort* s = Sort_val(sort);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkConst(*s), handle);
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
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPoint(*Term_val(sign), *Term_val(exp), *Term_val(sig)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value native_cvc5_stub_mk_fp(value v, uint32_t exp, uint32_t sig, value val){
  CAMLparam2(v, val);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPoint(exp, sig, *Term_val(val)), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp(value v, value sign, value exp, value sig){
  return native_cvc5_stub_mk_fp(v, Long_val(sign), Long_val(exp), sig);
}

CAMLprim value native_cvc5_stub_mk_fp_pos_inf(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPointPosInf(sign, exp), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_inf(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_inf(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPointNegInf(sign, exp), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_neg_inf(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_neg_inf(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_nan(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPointNaN(sign, exp), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_nan(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_nan(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_pos_zero(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPointPosZero(sign, exp), handle);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_fp_pos_zero(value v, value sign, value exp){
  return native_cvc5_stub_mk_fp_pos_zero(v, Long_val(sign), Long_val(exp));
}

CAMLprim value native_cvc5_stub_mk_fp_neg_zero(value v, uint32_t sign, uint32_t exp){
  CAMLparam1(v);
  CAMLlocal1(custom);
  TermManagerHandle* handle = TermManager_handle_val(v);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(handle->tm->mkFloatingPointNegZero(sign, exp), handle);
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
  CVC5_TRY_CATCH_BEGIN;
  std::vector<uint32_t> term_vec;
  size_t arity = Wosize_val(args);
  term_vec.reserve(arity);

  for (size_t i = 0; i < arity; i++)
    term_vec.emplace_back(Int_val(Field(args, i)));

  new(&op_operations, &custom)
    Op(TermManager_val(v)->mkOp((cvc5::Kind)Int_val(kind), term_vec));
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

CAMLprim value ocaml_cvc5_stub_solver_mk_grammar(value s, value t1, value t2){
  CAMLparam3(s, t1, t2);
  CAMLlocal1(custom);
  cvc5::Solver* solver = Solver_val(s);
  CVC5_TRY_CATCH_BEGIN;

  std::vector<cvc5::Term> nonterminal_vec;
  size_t arity1 = Wosize_val(t1);
  nonterminal_vec.reserve(arity1);
  for (size_t i = 0; i < arity1; i++) {
    nonterminal_vec.emplace_back(*Term_val(Field(t1, i)));
  }

  std::vector<cvc5::Term> rules_vec;
  size_t arity2 = Wosize_val(t2);
  rules_vec.reserve(arity2);
  for (size_t i = 0; i < arity2; i++) {
    rules_vec.emplace_back(*Term_val(Field(t2, i)));
  }

  new(&grammar_operations, &custom)
    Grammar(solver->mkGrammar(nonterminal_vec, rules_vec));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_synth_fun_grammar(value s, value tm, value name, value terms, value sort, value gram) {
  CAMLparam5(s, name, terms, sort, gram);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;

  std::vector<cvc5::Term> inputs;
  size_t arity = Wosize_val(terms);
  inputs.reserve(arity);

  for (size_t i = 0; i < arity; i++) {
    inputs.emplace_back(*Term_val(Field(terms, i)));
  }

  cvc5::Term fun = Solver_val(s)->synthFun(String_val(name), inputs, *(Sort_val(sort)), *(Grammar_val(gram)));

  new(&term_operations, &custom) Term(fun, TermManager_handle_val(tm));

  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synth_fun_unpack(value* argv, int argc) {
  return ocaml_cvc5_stub_solver_synth_fun_grammar(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

CAMLprim value ocaml_cvc5_stub_solver_synth_fun(value s, value tm, value name, value terms, value sort) {
  CAMLparam4(s, name, terms, sort);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;

  std::vector<cvc5::Term> inputs;
  size_t arity = Wosize_val(terms);
  inputs.reserve(arity);

  for (size_t i = 0; i < arity; i++) {
    inputs.emplace_back(*Term_val(Field(terms, i)));
  }

  cvc5::Term fun = Solver_val(s)->synthFun(String_val(name), inputs, *(Sort_val(sort)));

  new(&term_operations, &custom) Term(fun, TermManager_handle_val(tm));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_declare_sygus_var(value s, value name, value sort) {
  CAMLparam3(s, name, sort);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;

  cvc5::Term var = Solver_val(s)->declareSygusVar(String_val(name), *(Sort_val(sort)));

  new(&term_operations, &custom) Term(var, NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_add_sygus_constraint(value s, value term) {
  CAMLparam2(s, term);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(s)->addSygusConstraint(*(Term_val(term)));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_add_sygus_assume(value s, value term) {
  CAMLparam2(s, term);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(s)->addSygusAssume(*(Term_val(term)));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_check_synth(value s) {
  CAMLparam1(s);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&synthresult_operations, &custom) SynthResult(Solver_val(s)->checkSynth());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_add_rules(value gram, value term, value terms) {
  CAMLparam3(gram, term, terms);
  Grammar* grammar = Grammar_val(gram);
  CVC5_TRY_CATCH_BEGIN;

  std::vector<cvc5::Term> rules;
  size_t arity = Wosize_val(terms);
  rules.reserve(arity);

  for (size_t i = 0; i < arity; i++) {
    rules.emplace_back(*Term_val(Field(terms, i)));
  }

  grammar->addRules(*Term_val(term), rules);
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_synth_solution(value s, value term) {
  CAMLparam2(s, term);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  cvc5::Term sol = Solver_val(s)->getSynthSolution(*(Term_val(term)));
  new(&term_operations, &custom) Term(sol, NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synthresult_is_null(value res) {
  CAMLparam1(res);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Synthresult_val(res)->isNull()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synthresult_has_solution(value res) {
  CAMLparam1(res);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Synthresult_val(res)->hasSolution()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synthresult_no_solution(value res) {
  CAMLparam1(res);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Synthresult_val(res)->hasNoSolution()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synthresult_is_unknown(value res) {
  CAMLparam1(res);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(Val_bool(Synthresult_val(res)->isUnknown()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_synthresult_to_string(value res) {
  CAMLparam1(res);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Synthresult_val(res)->toString().data()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_result_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Result_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_result_get_unknown_explanation(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int((int)Result_val(v)->getUnknownExplanation());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_tm_get_statistics(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&statistics_operations, &custom) Statistics(TermManager_val(v)->getStatistics());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_param_sort(value tm, value name_opt){
  CAMLparam2(tm, name_opt);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::optional<std::string> name = std::nullopt;
  if (Is_block(name_opt)) {
    name = std::string(String_val(Field(name_opt, 0)));
  }
  new(&sort_operations, &custom) Sort(TermManager_val(tm)->mkParamSort(name));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_unresolved_datatype_sort(value tm, value name, value arity){
  CAMLparam3(tm, name, arity);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(TermManager_val(tm)->mkUnresolvedDatatypeSort(String_val(name), Int_val(arity)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_datatype_constructor_decl(value tm, value name){
  CAMLparam2(tm, name);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_constructor_decl_operations, &custom)
    DatatypeConstructorDecl(TermManager_val(tm)->mkDatatypeConstructorDecl(String_val(name)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_datatype_decl(value tm, value name, value is_codt){
  CAMLparam3(tm, name, is_codt);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_decl_operations, &custom)
    DatatypeDecl(TermManager_val(tm)->mkDatatypeDecl(String_val(name), Bool_val(is_codt)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_mk_datatype_decl_with_params(value tm, value name, value params, value is_codt){
  CAMLparam4(tm, name, params, is_codt);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec;
  size_t arity = Wosize_val(params);
  sort_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    sort_vec.emplace_back(*Sort_val(Field(params, i)));
  }
  new(&datatype_decl_operations, &custom)
    DatatypeDecl(TermManager_val(tm)->mkDatatypeDecl(String_val(name), sort_vec, Bool_val(is_codt)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_null, isNull)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_boolean, isBoolean)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_integer, isInteger)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_real, isReal)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_string, isString)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_regexp, isRegExp)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_rm, isRoundingMode)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_bv, isBitVector)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_fp, isFloatingPoint)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_datatype, isDatatype)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_datatype_constructor, isDatatypeConstructor)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_datatype_selector, isDatatypeSelector)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_datatype_tester, isDatatypeTester)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_function, isFunction)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_predicate, isPredicate)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_tuple, isTuple)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_nullable, isNullable)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_finite_field, isFiniteField)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_record, isRecord)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_array, isArray)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_set, isSet)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_bag, isBag)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_sequence, isSequence)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_abstract, isAbstract)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_uninterpreted_sort, isUninterpretedSort)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_uninterpreted_sort_constructor, isUninterpretedSortConstructor)
DEFINE_SORT_BOOL_STUB(ocaml_cvc5_stub_sort_is_instantiated, isInstantiated)

CAMLprim value ocaml_cvc5_stub_sort_get_uninterpreted_sort_constructor(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(Sort_val(v)->getUninterpretedSortConstructor());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_get_datatype(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_operations, &custom) Datatype(Sort_val(v)->getDatatype());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_instantiate(value v, value params){
  CAMLparam2(v, params);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec;
  size_t arity = Wosize_val(params);
  sort_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    sort_vec.emplace_back(*Sort_val(Field(params, i)));
  }
  new(&sort_operations, &custom) Sort(Sort_val(v)->instantiate(sort_vec));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_get_instantiated_parameters(value v){
  CAMLparam1(v);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> params = Sort_val(v)->getInstantiatedParameters();
  size_t n = params.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&sort_operations, &custom) Sort(params[i]);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_substitute(value v, value s, value repl){
  CAMLparam3(v, s, repl);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(Sort_val(v)->substitute(*Sort_val(s), *Sort_val(repl)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_sort_substitute_many(value v, value sorts, value repls){
  CAMLparam3(v, sorts, repls);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> sort_vec, repl_vec;
  size_t arity = Wosize_val(sorts);
  sort_vec.reserve(arity);
  repl_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    sort_vec.emplace_back(*Sort_val(Field(sorts, i)));
    repl_vec.emplace_back(*Sort_val(Field(repls, i)));
  }
  new(&sort_operations, &custom)
    Sort(Sort_val(v)->substitute(sort_vec, repl_vec));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_get_num_children(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Term_val(v)->getNumChildren());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_get_child(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term((*Term_val(v))[Int_val(i)], Term_val(v)->getManager());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_substitute(value v, value t, value repl){
  CAMLparam3(v, t, repl);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Term_val(v)->substitute(*Term_val(t), *Term_val(repl)), Term_val(v)->getManager());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_substitute_many(value v, value terms, value repls){
  CAMLparam3(v, terms, repls);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> term_vec, repl_vec;
  size_t arity = Wosize_val(terms);
  term_vec.reserve(arity);
  repl_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    term_vec.emplace_back(*Term_val(Field(terms, i)));
    repl_vec.emplace_back(*Term_val(Field(repls, i)));
  }
  new(&term_operations, &custom)
    Term(Term_val(v)->substitute(term_vec, repl_vec), Term_val(v)->getManager());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

DEFINE_TERM_BOOL_STUB(ocaml_cvc5_stub_term_has_op, hasOp)
DEFINE_TERM_BOOL_STUB(ocaml_cvc5_stub_term_has_symbol, hasSymbol)
DEFINE_TERM_BOOL_STUB(ocaml_cvc5_stub_term_is_null, isNull)
DEFINE_TERM_UNARY_STUB(ocaml_cvc5_stub_term_not_term, notTerm)
DEFINE_TERM_BINARY_STUB(ocaml_cvc5_stub_term_and_term, andTerm)
DEFINE_TERM_BINARY_STUB(ocaml_cvc5_stub_term_or_term, orTerm)
DEFINE_TERM_BINARY_STUB(ocaml_cvc5_stub_term_xor_term, xorTerm)
DEFINE_TERM_BINARY_STUB(ocaml_cvc5_stub_term_eq_term, eqTerm)
DEFINE_TERM_BINARY_STUB(ocaml_cvc5_stub_term_imp_term, impTerm)

CAMLprim value ocaml_cvc5_stub_term_get_op(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&op_operations, &custom) Op(Term_val(v)->getOp());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_get_symbol(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Term_val(v)->getSymbol().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_term_ite_term(value v, value t, value e){
  CAMLparam3(v, t, e);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Term_val(v)->iteTerm(*Term_val(t), *Term_val(e)), Term_val(v)->getManager());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_add_rule(value gram, value term, value rule) {
  CAMLparam3(gram, term, rule);
  CVC5_TRY_CATCH_BEGIN;
  Grammar_val(gram)->addRule(*Term_val(term), *Term_val(rule));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_add_any_constant(value gram, value term) {
  CAMLparam2(gram, term);
  CVC5_TRY_CATCH_BEGIN;
  Grammar_val(gram)->addAnyConstant(*Term_val(term));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_add_any_variable(value gram, value term) {
  CAMLparam2(gram, term);
  CVC5_TRY_CATCH_BEGIN;
  Grammar_val(gram)->addAnyVariable(*Term_val(term));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_is_null(value gram) {
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Grammar_val(gram)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_grammar_to_string(value gram) {
  CAMLparam1(gram);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Grammar_val(gram)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_datatype_constructor_decl(value v){
  CVC5_TRY_CATCH_BEGIN;
  datatype_constructor_decl_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_equal(value v1, value v2){
  return Val_bool(*DatatypeConstructorDecl_val(v1) == *DatatypeConstructorDecl_val(v2));
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_add_selector(value v, value name, value sort){
  CAMLparam3(v, name, sort);
  CVC5_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl_val(v)->addSelector(String_val(name), *Sort_val(sort));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_add_selector_self(value v, value name){
  CAMLparam2(v, name);
  CVC5_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl_val(v)->addSelectorSelf(String_val(name));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_add_selector_unresolved(value v, value name, value dtname){
  CAMLparam3(v, name, dtname);
  CVC5_TRY_CATCH_BEGIN;
  DatatypeConstructorDecl_val(v)->addSelectorUnresolved(String_val(name), String_val(dtname));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeConstructorDecl_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_decl_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeConstructorDecl_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_datatype_decl(value v){
  CVC5_TRY_CATCH_BEGIN;
  datatype_decl_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_equal(value v1, value v2){
  return Val_bool(*DatatypeDecl_val(v1) == *DatatypeDecl_val(v2));
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_add_constructor(value v, value ctor){
  CAMLparam2(v, ctor);
  CVC5_TRY_CATCH_BEGIN;
  DatatypeDecl_val(v)->addConstructor(*DatatypeConstructorDecl_val(ctor));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_get_num_constructors(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(DatatypeDecl_val(v)->getNumConstructors());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_is_parametric(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeDecl_val(v)->isParametric());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_is_resolved(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeDecl_val(v)->isResolved());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeDecl_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeDecl_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_decl_get_name(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeDecl_val(v)->getName().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_datatype_selector(value v){
  CVC5_TRY_CATCH_BEGIN;
  datatype_selector_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_equal(value v1, value v2){
  return Val_bool(*DatatypeSelector_val(v1) == *DatatypeSelector_val(v2));
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_get_name(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeSelector_val(v)->getName().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_get_term(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(DatatypeSelector_val(v)->getTerm(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_get_updater_term(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(DatatypeSelector_val(v)->getUpdaterTerm(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_get_codomain_sort(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom) Sort(DatatypeSelector_val(v)->getCodomainSort());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeSelector_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_selector_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeSelector_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_datatype_constructor(value v){
  CVC5_TRY_CATCH_BEGIN;
  datatype_constructor_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_equal(value v1, value v2){
  return Val_bool(*DatatypeConstructor_val(v1) == *DatatypeConstructor_val(v2));
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_name(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeConstructor_val(v)->getName().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_term(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(DatatypeConstructor_val(v)->getTerm(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_instantiated_term(value v, value sort){
  CAMLparam2(v, sort);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(DatatypeConstructor_val(v)->getInstantiatedTerm(*Sort_val(sort)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_tester_term(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(DatatypeConstructor_val(v)->getTesterTerm(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_num_selectors(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(DatatypeConstructor_val(v)->getNumSelectors());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_selector_at(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_selector_operations, &custom)
    DatatypeSelector((*DatatypeConstructor_val(v))[Int_val(i)]);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_get_selector(value v, value name){
  CAMLparam2(v, name);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_selector_operations, &custom)
    DatatypeSelector(DatatypeConstructor_val(v)->getSelector(String_val(name)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(DatatypeConstructor_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_constructor_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(DatatypeConstructor_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_datatype(value v){
  CVC5_TRY_CATCH_BEGIN;
  datatype_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_equal(value v1, value v2){
  return Val_bool(*Datatype_val(v1) == *Datatype_val(v2));
}

CAMLprim value ocaml_cvc5_stub_datatype_get_constructor_at(value v, value i){
  CAMLparam2(v, i);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_constructor_operations, &custom)
    DatatypeConstructor((*Datatype_val(v))[Int_val(i)]);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_get_constructor(value v, value name){
  CAMLparam2(v, name);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_constructor_operations, &custom)
    DatatypeConstructor(Datatype_val(v)->getConstructor(String_val(name)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_get_selector(value v, value name){
  CAMLparam2(v, name);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&datatype_selector_operations, &custom)
    DatatypeSelector(Datatype_val(v)->getSelector(String_val(name)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_get_name(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Datatype_val(v)->getName().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_get_num_constructors(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int(Datatype_val(v)->getNumConstructors());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_get_parameters(value v){
  CAMLparam1(v);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Sort> params = Datatype_val(v)->getParameters();
  size_t n = params.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&sort_operations, &custom) Sort(params[i]);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_parametric(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isParametric());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_codatatype(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isCodatatype());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_tuple(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isTuple());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_record(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isRecord());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_finite(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isFinite());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_well_founded(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isWellFounded());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Datatype_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_datatype_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Datatype_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_sort(value slv, value symbol, value arity, value fresh){
  CAMLparam4(slv, symbol, arity, fresh);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&sort_operations, &custom)
    Sort(Solver_val(slv)->declareSort(String_val(symbol), Int_val(arity), Bool_val(fresh)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_datatype(value slv, value symbol, value ctors){
  CAMLparam3(slv, symbol, ctors);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::DatatypeConstructorDecl> ctor_vec;
  size_t arity = Wosize_val(ctors);
  ctor_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    ctor_vec.emplace_back(*DatatypeConstructorDecl_val(Field(ctors, i)));
  }
  new(&sort_operations, &custom)
    Sort(Solver_val(slv)->declareDatatype(String_val(symbol), ctor_vec));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_define_fun_rec(value slv, value symbol, value vars, value s, value body, value global){
  CAMLparam5(slv, symbol, vars, s, body);
  CAMLxparam1(global);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> var_vec;
  size_t arity = Wosize_val(vars);
  var_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    var_vec.emplace_back(*Term_val(Field(vars, i)));
  }
  new(&term_operations, &custom)
    Term(Solver_val(slv)->defineFunRec(String_val(symbol), var_vec, *Sort_val(s), *Term_val(body), Bool_val(global)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_define_fun_rec_bytecode(value* argv, int argc){
  return ocaml_cvc5_stub_define_fun_rec(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5]);
}

CAMLprim value ocaml_cvc5_stub_define_fun_rec_term(value slv, value fun, value vars, value body, value global){
  CAMLparam5(slv, fun, vars, body, global);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> var_vec;
  size_t arity = Wosize_val(vars);
  var_vec.reserve(arity);
  for (size_t i = 0; i < arity; ++i) {
    var_vec.emplace_back(*Term_val(Field(vars, i)));
  }
  new(&term_operations, &custom)
    Term(Solver_val(slv)->defineFunRec(*Term_val(fun), var_vec, *Term_val(body), Bool_val(global)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_define_funs_rec(value slv, value funs, value bvs, value terms, value global){
  CAMLparam5(slv, funs, bvs, terms, global);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> fun_vec;
  std::vector<std::vector<cvc5::Term>> bound_var_vec;
  std::vector<cvc5::Term> term_vec;
  size_t n = Wosize_val(funs);
  fun_vec.reserve(n);
  bound_var_vec.reserve(n);
  term_vec.reserve(n);
  for (size_t i = 0; i < n; ++i) {
    fun_vec.emplace_back(*Term_val(Field(funs, i)));
    value inner = Field(bvs, i);
    std::vector<cvc5::Term> inner_vec;
    size_t m = Wosize_val(inner);
    inner_vec.reserve(m);
    for (size_t j = 0; j < m; ++j) {
      inner_vec.emplace_back(*Term_val(Field(inner, j)));
    }
    bound_var_vec.push_back(inner_vec);
    term_vec.emplace_back(*Term_val(Field(terms, i)));
  }
  Solver_val(slv)->defineFunsRec(fun_vec, bound_var_vec, term_vec, Bool_val(global));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_assertions(value slv){
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> assertions = Solver_val(slv)->getAssertions();
  size_t n = assertions.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(assertions[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_info(value slv, value flag){
  CAMLparam2(slv, flag);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Solver_val(slv)->getInfo(String_val(flag)).c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_option(value slv, value opt){
  CAMLparam2(slv, opt);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Solver_val(slv)->getOption(String_val(opt)).c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_option_names(value slv){
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<std::string> names = Solver_val(slv)->getOptionNames();
  size_t n = names.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    Store_field(result, i, caml_copy_string(names[i].c_str()));
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_option_info(value slv, value opt){
  CAMLparam2(slv, opt);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  custom = caml_alloc_custom(&option_info_operations, sizeof(OptionInfo), 0, 1);
  OptionInfo_val(custom) = new cvc5::OptionInfo(Solver_val(slv)->getOptionInfo(String_val(opt)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_unsat_assumptions(value slv){
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms = Solver_val(slv)->getUnsatAssumptions();
  size_t n = terms.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(terms[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_unsat_core_lemmas(value slv){
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms = Solver_val(slv)->getUnsatCoreLemmas();
  size_t n = terms.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(terms[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_difficulty(value slv){
  CAMLparam1(slv);
  CAMLlocal2(result, pair);
  CVC5_TRY_CATCH_BEGIN;
  std::map<cvc5::Term, cvc5::Term> difficulty = Solver_val(slv)->getDifficulty();
  result = caml_alloc(difficulty.size(), 0);
  size_t i = 0;
  for (const auto& entry : difficulty) {
    value lhs = Val_unit;
    value rhs = Val_unit;
    new(&term_operations, &lhs) Term(entry.first, NULL);
    new(&term_operations, &rhs) Term(entry.second, NULL);
    pair = caml_alloc_tuple(2);
    Store_field(pair, 0, lhs);
    Store_field(pair, 1, rhs);
    Store_field(result, i++, pair);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

static value alloc_timeout_core(const std::pair<cvc5::Result, std::vector<cvc5::Term>>& core){
  CAMLparam0();
  CAMLlocal3(result_pair, result_value, terms_value);
  result_pair = caml_alloc_tuple(2);
  new(&result_operations, &result_value) Result(core.first);
  size_t n = core.second.size();
  terms_value = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(core.second[i], NULL);
    Store_field(terms_value, i, custom);
  }
  Store_field(result_pair, 0, result_value);
  Store_field(result_pair, 1, terms_value);
  CAMLreturn(result_pair);
}

CAMLprim value ocaml_cvc5_stub_get_timeout_core(value slv){
  CAMLparam1(slv);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(alloc_timeout_core(Solver_val(slv)->getTimeoutCore()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_timeout_core_assuming(value slv, value assumptions){
  CAMLparam2(slv, assumptions);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> term_vec;
  size_t n = Wosize_val(assumptions);
  term_vec.reserve(n);
  for (size_t i = 0; i < n; ++i) {
    term_vec.emplace_back(*Term_val(Field(assumptions, i)));
  }
  CAMLreturn(alloc_timeout_core(Solver_val(slv)->getTimeoutCoreAssuming(term_vec)));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_proof(value slv, value component){
  CAMLparam2(slv, component);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Proof> proofs =
    Solver_val(slv)->getProof((cvc5::modes::ProofComponent)Int_val(component));
  size_t n = proofs.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&proof_operations, &custom) Proof(proofs[i]);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_proof_to_string(value slv, value proof, value format){
  CAMLparam3(slv, proof, format);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(
    Solver_val(slv)->proofToString(*Proof_val(proof), (cvc5::modes::ProofFormat)Int_val(format)).c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_learned_literals(value slv, value lit_type){
  CAMLparam2(slv, lit_type);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms =
    Solver_val(slv)->getLearnedLiterals((cvc5::modes::LearnedLitType)Int_val(lit_type));
  size_t n = terms.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(terms[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_quantifier_elimination(value slv, value q){
  CAMLparam2(slv, q);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getQuantifierElimination(*Term_val(q)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_quantifier_elimination_disjunct(value slv, value q){
  CAMLparam2(slv, q);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getQuantifierEliminationDisjunct(*Term_val(q)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_sep_heap(value slv, value loc, value data){
  CAMLparam3(slv, loc, data);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(slv)->declareSepHeap(*Sort_val(loc), *Sort_val(data));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_value_sep_heap(value slv){
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getValueSepHeap(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_value_sep_nil(value slv){
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getValueSepNil(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_declare_pool(value slv, value symbol, value sort, value init){
  CAMLparam4(slv, symbol, sort, init);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> init_vec;
  size_t n = Wosize_val(init);
  init_vec.reserve(n);
  for (size_t i = 0; i < n; ++i) {
    init_vec.emplace_back(*Term_val(Field(init, i)));
  }
  new(&term_operations, &custom)
    Term(Solver_val(slv)->declarePool(String_val(symbol), *Sort_val(sort), init_vec), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_set_info(value slv, value key, value val){
  CAMLparam3(slv, key, val);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(slv)->setInfo(String_val(key), String_val(val));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_is_logic_set(value slv){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Solver_val(slv)->isLogicSet());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_logic(value slv){
  CAMLparam1(slv);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Solver_val(slv)->getLogic().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_interpolant(value slv, value conj){
  CAMLparam2(slv, conj);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getInterpolant(*Term_val(conj)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_interpolant_grammar(value slv, value conj, value grammar){
  CAMLparam3(slv, conj, grammar);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(slv)->getInterpolant(*Term_val(conj), *Grammar_val(grammar)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_interpolant_next(value slv){
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getInterpolantNext(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_abduct(value slv, value conj){
  CAMLparam2(slv, conj);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getAbduct(*Term_val(conj)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_abduct_grammar(value slv, value conj, value grammar){
  CAMLparam3(slv, conj, grammar);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(slv)->getAbduct(*Term_val(conj), *Grammar_val(grammar)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_abduct_next(value slv){
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Solver_val(slv)->getAbductNext(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_block_model(value slv, value mode){
  CAMLparam2(slv, mode);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(slv)->blockModel((cvc5::modes::BlockModelsMode)Int_val(mode));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_block_model_values(value slv, value terms){
  CAMLparam2(slv, terms);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> term_vec;
  size_t n = Wosize_val(terms);
  term_vec.reserve(n);
  for (size_t i = 0; i < n; ++i) {
    term_vec.emplace_back(*Term_val(Field(terms, i)));
  }
  Solver_val(slv)->blockModelValues(term_vec);
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_get_instantiations(value slv){
  CAMLparam1(slv);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Solver_val(slv)->getInstantiations().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_statistics(value slv){
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&statistics_operations, &custom) Statistics(Solver_val(slv)->getStatistics());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_sygus_constraints(value slv) {
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms = Solver_val(slv)->getSygusConstraints();
  size_t n = terms.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(terms[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_sygus_assumptions(value slv) {
  CAMLparam1(slv);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> terms = Solver_val(slv)->getSygusAssumptions();
  size_t n = terms.size();
  result = caml_alloc(n, 0);
  for (size_t i = 0; i < n; ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(terms[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_add_sygus_inv_constraint(value slv, value inv, value pre, value trans, value post) {
  CAMLparam5(slv, inv, pre, trans, post);
  CVC5_TRY_CATCH_BEGIN;
  Solver_val(slv)->addSygusInvConstraint(*Term_val(inv), *Term_val(pre), *Term_val(trans), *Term_val(post));
  CAMLreturn(Val_unit);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_check_synth_next(value slv) {
  CAMLparam1(slv);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&synthresult_operations, &custom) SynthResult(Solver_val(slv)->checkSynthNext());
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_get_synth_solutions(value slv, value terms) {
  CAMLparam2(slv, terms);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> term_vec;
  size_t n = Wosize_val(terms);
  term_vec.reserve(n);
  for (size_t i = 0; i < n; ++i) {
    term_vec.emplace_back(*Term_val(Field(terms, i)));
  }
  std::vector<cvc5::Term> sols = Solver_val(slv)->getSynthSolutions(term_vec);
  result = caml_alloc(sols.size(), 0);
  for (size_t i = 0; i < sols.size(); ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(sols[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_find_synth(value slv, value target) {
  CAMLparam2(slv, target);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(slv)->findSynth((cvc5::modes::FindSynthTarget)Int_val(target)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_solver_find_synth_grammar(value slv, value target, value grammar) {
  CAMLparam3(slv, target, grammar);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom)
    Term(Solver_val(slv)->findSynth((cvc5::modes::FindSynthTarget)Int_val(target), *Grammar_val(grammar)), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_proof(value v){
  CVC5_TRY_CATCH_BEGIN;
  proof_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_proof_equal(value v1, value v2){
  return Val_bool(*Proof_val(v1) == *Proof_val(v2));
}

CAMLprim value ocaml_cvc5_stub_proof_is_null(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(Proof_val(v)->isNull());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_proof_get_result(value v){
  CAMLparam1(v);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&term_operations, &custom) Term(Proof_val(v)->getResult(), NULL);
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_proof_get_children(value v){
  CAMLparam1(v);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Proof> children = Proof_val(v)->getChildren();
  result = caml_alloc(children.size(), 0);
  for (size_t i = 0; i < children.size(); ++i) {
    value custom = Val_unit;
    new(&proof_operations, &custom) Proof(children[i]);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_proof_get_arguments(value v){
  CAMLparam1(v);
  CAMLlocal1(result);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<cvc5::Term> args = Proof_val(v)->getArguments();
  result = caml_alloc(args.size(), 0);
  for (size_t i = 0; i < args.size(); ++i) {
    value custom = Val_unit;
    new(&term_operations, &custom) Term(args[i], NULL);
    Store_field(result, i, custom);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_option_info(value v){
  CVC5_TRY_CATCH_BEGIN;
  option_info_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(OptionInfo_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_name(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(OptionInfo_val(v)->name.c_str()));
  CVC5_TRY_CATCH_END;
}

static value alloc_string_array(const std::vector<std::string>& vec){
  CAMLparam0();
  CAMLlocal1(result);
  result = caml_alloc(vec.size(), 0);
  for (size_t i = 0; i < vec.size(); ++i) {
    Store_field(result, i, caml_copy_string(vec[i].c_str()));
  }
  CAMLreturn(result);
}

CAMLprim value ocaml_cvc5_stub_option_info_aliases(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(alloc_string_array(OptionInfo_val(v)->aliases));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_no_supports(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(alloc_string_array(OptionInfo_val(v)->noSupports));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_set_by_user(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(OptionInfo_val(v)->setByUser);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_category(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_int((int)OptionInfo_val(v)->category);
  CVC5_TRY_CATCH_END;
}

#define OPTION_INFO_HOLDS(name, alt) \
  CAMLprim value name(value v){ \
    CVC5_TRY_CATCH_BEGIN; \
    return Val_bool(std::holds_alternative<alt>(OptionInfo_val(v)->valueInfo)); \
    CVC5_TRY_CATCH_END; \
  }

OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_bool, cvc5::OptionInfo::ValueInfo<bool>)
OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_string, cvc5::OptionInfo::ValueInfo<std::string>)
OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_int, cvc5::OptionInfo::NumberInfo<int64_t>)
OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_uint, cvc5::OptionInfo::NumberInfo<uint64_t>)
OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_double, cvc5::OptionInfo::NumberInfo<double>)
OPTION_INFO_HOLDS(ocaml_cvc5_stub_option_info_is_mode, cvc5::OptionInfo::ModeInfo)

CAMLprim value ocaml_cvc5_stub_option_info_bool_value(value v){
  CVC5_TRY_CATCH_BEGIN;
  return Val_bool(OptionInfo_val(v)->boolValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_string_value(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(OptionInfo_val(v)->stringValue().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_int_value(value v){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_int64(OptionInfo_val(v)->intValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_uint_value(value v){
  CVC5_TRY_CATCH_BEGIN;
  return caml_copy_int64(OptionInfo_val(v)->uintValue());
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_option_info_double_value(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_double(OptionInfo_val(v)->doubleValue()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_delete_stat(value v){
  CVC5_TRY_CATCH_BEGIN;
  stat_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_stat_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Stat_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_stat_is_internal(value v){ return Val_bool(Stat_val(v)->isInternal()); }
CAMLprim value ocaml_cvc5_stub_stat_is_default(value v){ return Val_bool(Stat_val(v)->isDefault()); }
CAMLprim value ocaml_cvc5_stub_stat_is_int(value v){ return Val_bool(Stat_val(v)->isInt()); }
CAMLprim value ocaml_cvc5_stub_stat_get_int(value v){ return caml_copy_int64(Stat_val(v)->getInt()); }
CAMLprim value ocaml_cvc5_stub_stat_is_double(value v){ return Val_bool(Stat_val(v)->isDouble()); }

CAMLprim value ocaml_cvc5_stub_stat_get_double(value v){
  CAMLparam1(v);
  CAMLreturn(caml_copy_double(Stat_val(v)->getDouble()));
}

CAMLprim value ocaml_cvc5_stub_stat_is_string(value v){ return Val_bool(Stat_val(v)->isString()); }

CAMLprim value ocaml_cvc5_stub_stat_get_string(value v){
  CAMLparam1(v);
  CAMLreturn(caml_copy_string(Stat_val(v)->getString().c_str()));
}

CAMLprim value ocaml_cvc5_stub_stat_is_histogram(value v){ return Val_bool(Stat_val(v)->isHistogram()); }

CAMLprim value ocaml_cvc5_stub_stat_get_histogram(value v){
  CAMLparam1(v);
  CAMLlocal2(result, pair);
  const auto& hist = Stat_val(v)->getHistogram();
  result = caml_alloc(hist.size(), 0);
  size_t i = 0;
  for (const auto& entry : hist) {
    pair = caml_alloc_tuple(2);
    Store_field(pair, 0, caml_copy_string(entry.first.c_str()));
    Store_field(pair, 1, caml_copy_int64(entry.second));
    Store_field(result, i++, pair);
  }
  CAMLreturn(result);
}

CAMLprim value ocaml_cvc5_stub_delete_statistics(value v){
  CVC5_TRY_CATCH_BEGIN;
  statistics_delete(v);
  return Val_unit;
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_statistics_to_string(value v){
  CAMLparam1(v);
  CVC5_TRY_CATCH_BEGIN;
  CAMLreturn(caml_copy_string(Statistics_val(v)->toString().c_str()));
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_statistics_get(value v, value name){
  CAMLparam2(v, name);
  CAMLlocal1(custom);
  CVC5_TRY_CATCH_BEGIN;
  new(&stat_operations, &custom) Stat(Statistics_val(v)->get(String_val(name)));
  CAMLreturn(custom);
  CVC5_TRY_CATCH_END;
}

CAMLprim value ocaml_cvc5_stub_statistics_entries(value v){
  CAMLparam1(v);
  CAMLlocal2(result, pair);
  CVC5_TRY_CATCH_BEGIN;
  std::vector<std::pair<std::string, cvc5::Stat>> entries;
  for (auto it = Statistics_val(v)->begin(true, true); it != Statistics_val(v)->end(); ++it) {
    entries.emplace_back(it->first, it->second);
  }
  result = caml_alloc(entries.size(), 0);
  for (size_t i = 0; i < entries.size(); ++i) {
    value stat_custom = Val_unit;
    new(&stat_operations, &stat_custom) Stat(entries[i].second);
    pair = caml_alloc_tuple(2);
    Store_field(pair, 0, caml_copy_string(entries[i].first.c_str()));
    Store_field(pair, 1, stat_custom);
    Store_field(result, i, pair);
  }
  CAMLreturn(result);
  CVC5_TRY_CATCH_END;
}

} // extern "C"
