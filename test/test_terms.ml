open Cvc5

let tm = TermManager.mk_tm ()

let solver = Solver.mk_solver tm

let int_sort = Sort.mk_int_sort tm

let zero = Term.mk_int tm 0

let x = Term.mk_const_s tm int_sort "x"

let x_gt_zero = Term.mk_term tm Kind.Geq [| x; zero |]

(* x >= 0 and ~(~(x >= 0) should be considered equal terms after simplications *)
let () =
  let x_gt_zero_not = Term.mk_term tm Kind.Not [| x_gt_zero |] in
  let x_gt_zero_not_not = Term.mk_term tm Kind.Not [| x_gt_zero_not |] in
  let simplified = Solver.simplify solver x_gt_zero_not_not in
  assert (Term.equal x_gt_zero simplified)

(* Different terms should not be considered equal *)
let () =
  let false_const = Term.mk_false tm in
  assert (not (Term.equal false_const x_gt_zero))

(* Term.kind returns the correct Kind of a term *)
let () =
  assert (Term.kind x_gt_zero = Kind.Geq);
  assert (not (Term.kind x_gt_zero = Kind.Not))
