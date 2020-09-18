import .HNN_normalize

open free_group multiplicative P semidirect_product
variables {ι : Type} [decidable_eq ι] (T : set ι) [decidable_pred T]

meta def exp_sum_eq_zero (t x : ι)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (cyc_r : free_group ι) :
  solver cyc_r T := λ w,
let (c₂, conj_r) := cyclically_conjugate x cyc_r in
let r' := (add_subscript t conj_r).left in
let (a, b) := min_max_subscript x r' in
do (p, n) ← HNN_normalize t x r' a b hs w,
if t ∈ T
  then let T' : set (ι × C∞) := { i : ι × C∞ | i.1 ∈ T } in
    do np ← hs r' T' p.right,
    return (change_r (c₂⁻¹)
      (inr (of' t n) * P.map (remove_subscript t) sorry (P.trans p np)))
      -- (P.map (remove_subscript t) sorry (P.trans p np))
      --  inr (of' t n))
  -- case t ∉ T
  else
    -- Kind of silly but oh well. Could check if n = 1 before normalization.
    if n ≠ 1 then none
      else let T' : set (ι × C∞) := { i : ι × C∞ | i.1 ∈ T ∧ i.2 = 1 } in
        do np ← hs r' T' p.right,
        return (change_r (c₂⁻¹) (P.map (remove_subscript t) sorry (P.trans p np)))