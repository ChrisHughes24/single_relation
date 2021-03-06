import pow_single_pullback
import exp_sum_eq_zero
/-!
# No exponent sum equal to zero

The case when there is no exponent sum equal to zero for the one relator algorithm.
-/
open free_group multiplicative
variables {ι : Type} [decidable_eq ι] (r : free_group ι) (T : set ι) [decidable_pred T]
variables (t x : ι)

/-- `psi1 t x α` sends `of x` to `of x * of' t (α⁻¹)` and all other letters to themselves  -/
meta def psi1 (α : C∞) : free_group ι ≃* free_group ι :=
{ to_fun := free_group.lift'
    (λ i, if i = x
            then gpowers_hom _ (of x * of' t (α⁻¹))
            else of' i),
  inv_fun := free_group.lift'
    (λ i, if i = x
            then gpowers_hom _ (of x * of' t α)
            else of' i),
  left_inv := undefined,
  right_inv := undefined,
  map_mul' := by simp }

/-- `psi t x α β` sends `of x` to `of x * of' t (α⁻¹)`, `of t` to `of' t β` and all other
  letters to themselves.    -/
def psi (t x : ι) (α β : C∞) : free_group ι →* free_group ι :=
free_group.lift'
  (λ i,
    if i = x
    then gpowers_hom _ (of x * of' t (α⁻¹))
    else if i = t
      then { to_fun := λ n, of' i (of_add (to_add β * to_add n)),
             map_one' := by simp,
             map_mul' := by simp [of'_eq_of_pow, gpow_mul, gpow_add] }
      else of' i)

/-- `exp_sum_ne_zero t x α β hs cyc_r` solves the one relator problem for `cyc_r` and `T`,
  when the exponent sum of `t` in `cyc_r` is `α` and the exponent sum, of `x` in `cyc_r` is `β`.
  `cyc_r` must be cyclically reduced. -/
meta def exp_sum_ne_zero (t x : ι) (α β : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (cyc_r : free_group ι) : solver cyc_r T :=
λ w, do p ← exp_sum_eq_zero T t x hs (psi t x α β cyc_r) (psi t x α β w),
pow_single_pullback t β (P.map (psi1 t x α).symm.to_monoid_hom undefined p)
