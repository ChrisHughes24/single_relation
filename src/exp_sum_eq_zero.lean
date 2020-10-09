import HNN_normalize
import cyclically_reduce
/-!
# Exp sum equal to zero
The case when there is a `t` in the relation with exponent sum equal to zero

## Main definitions
The main definition is `exp_sum_eq_zero`, which solves the word problem in the case
when there is a `t` with exponent_sum 0 in `r`.
-/
open free_group multiplicative P semidirect_product
variables {ι : Type} [decidable_eq ι] (T : set ι) [decidable_pred T]

/-- `exp_sum_eq_zero T t x hs cyc_r` solves the word problem for `cyc_r` and `T`
  when `t` has exponent sum zero in `cyc_r`, `cyc_r` is cyclically reduced and
  `t ∈ T → x ∉ T` and `x ≠ t` -/
@[inline] meta def exp_sum_eq_zero (t x : ι)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (cyc_r : free_group ι) : solver cyc_r T :=
λ w,
let (c₂, conj_r) := cyclically_conjugate x cyc_r in
let r' := (add_subscript t conj_r).left in
let (a, b) := min_max_subscript x r' in
do (p, n) ← HNN_normalize t x r' a b hs w,
if t ∈ T
  then let T' : set (ι × C∞) := { i : ι × C∞ | i.1 ∈ T } in
    do np ← hs r' T' p.right,
    return (change_r c₂
      (inr (of' t n) * P.map (remove_subscript t) undefined (P.trans p np)))
  -- case t ∉ T
  else
    -- Kind of silly. Could check if n = 1 before normalization.
    if n ≠ 1 then none
      else let T' : set (ι × C∞) := { i : ι × C∞ | i.1 ∈ T ∧ i.2 = 1 } in
        do np ← hs r' T' p.right,
        return (change_r c₂ (P.map (remove_subscript t) undefined (P.trans p np)))
