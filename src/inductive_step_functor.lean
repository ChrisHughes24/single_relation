import for_mathlib.coprod.free_group_subgroup
import .functor
import .cyclically_reduce
import .initial
import tactic

noncomputable theory

notation `C∞` := multiplicative ℤ

universe u

variables {ι : Type} [decidable_eq ι] (r : free_group ι) (T : set ι) [decidable_pred T]

open free_group P semidirect_product multiplicative

def mul_subscript : C∞ →* free_group (ι × C∞) ≃* free_group (ι × C∞) :=
{ to_fun := λ n, free_group.equiv (equiv.prod_congr (equiv.refl _) (mul_left n)),
  map_one' := sorry,
  map_mul' := sorry }

def add_subscript (t : ι) : free_group ι →* free_group (ι × C∞) ⋊[mul_subscript] C∞ :=
free_group.lift' (λ j,
  if t = j
  then semidirect_product.inr
  else semidirect_product.inl.comp (of' (j, 1)))

def remove_subscript (t : ι) : free_group (ι × C∞) →* free_group ι :=
free_group.lift' (λ g, (mul_aut.conj (of' t g.2)).to_monoid_hom.comp (of' g.1))

@[simp] lemma remove_subscript_comp_mul_subscript (t : ι) (n : C∞) :
  (remove_subscript t).comp (@mul_subscript ι _ n).to_monoid_hom =
  (mul_aut.conj (of' t n)).to_monoid_hom.comp (remove_subscript t) :=
free_group.hom_ext
  (by simp [remove_subscript, mul_subscript, lift'_eq_lift, of'_eq_of_pow, gpow_add, mul_assoc])

@[simp] lemma remove_subscript_mul_subscript (t : ι) (n : C∞) (x) : remove_subscript t
  (mul_subscript n x) =  of' t n * remove_subscript t x * of' t n⁻¹ :=
by simpa [-remove_subscript_comp_mul_subscript] using monoid_hom.ext_iff.1
  (remove_subscript_comp_mul_subscript t n) x

@[simp] lemma remove_subscript_mul_subscript_inv (t : ι) (n : C∞) (x) : remove_subscript t
  ((mul_subscript n)⁻¹ x) = of' t n⁻¹ * remove_subscript t x * of' t n :=
by rw [← monoid_hom.map_inv, remove_subscript_mul_subscript, inv_inv, mul_assoc]

@[simp] lemma remove_subscript_of' (t : ι) (l : ι × C∞) (n : C∞) : remove_subscript t (of' l n) =
  (mul_aut.conj (of' t l.2)) (of' l.1 n) :=
free_group.lift'_of' _ _ _

def remove_subscript_SD (t : ι) : free_group (ι ×C∞) ⋊[mul_subscript] C∞ →* free_group ι :=
semidirect_product.lift (remove_subscript t) (of' t)
  (λ g, hom_ext (λ j, by simp [mul_aut.conj_apply, mul_assoc]))

include r

lemma lhs_eq_of_mem {n : solver r T}
  {x : free_group ι} {y : P (free_group ι)}
  (h : y ∈ n x) : lhs r y = x := sorry

lemma lhs_inl_eq_of_mem {n : solver r T}
  {x : free_group ι} {y : P (free_group ι)}
  (h : y ∈ n x) : lhs r (inl y.left) = x * y.right⁻¹ :=
by rw [eq_mul_inv_iff_mul_eq, ← lhs_inr y.right, ← monoid_hom.map_mul,
    inl_left_mul_inr_right, lhs_eq_of_mem r T h]

variable {ι}

omit r

noncomputable def normalize_cons
  (t : ι) (r' : free_group (ι × C∞))
  {A B : set (ι × C∞)}
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) :
  Π (old1 : free_group (ι × C∞)) --contains no t
  (old2 : P (free_group (ι × C∞))),
  P (free_group (ι × C∞))
| old1 ⟨w, ⟨[], _⟩⟩     := ⟨mul_free old1 w, old1⟩
| old1 ⟨w, ⟨i :: l, _⟩⟩ :=
  if i.1.1 = t
  then if i.2 ≤ 1
    then option.elim (hA old1)
      (inr old1 * ⟨w, ⟨i :: l, sorry⟩⟩)
      (λ a, inr (of (t, 1))⁻¹ *
        normalize_cons (mul_subscript (of_add 1) (right_hom a))
          ⟨mul_free (of (t, 1)) (mul_free a.right⁻¹ a.left * w),
            of' (t, 1) (of_add 1 * i.2) * ⟨l, sorry⟩⟩)
    else option.elim (hB old1)
      (inr old1 * ⟨w, ⟨i :: l, sorry⟩⟩)
      (λ a, inr (of (t, 1)) *
        normalize_cons (mul_subscript (of_add (-1)) (right_hom a))
          ⟨mul_free (of (t, 1))⁻¹ (mul_free a.right⁻¹ a.left * w), of' i.1 (of_add (-1) * i.2) *⟨l, sorry⟩⟩)
  else normalize_cons ⟨old1.1 ++ [i], sorry⟩ ⟨(mul_free (of' i.1 i.2))⁻¹ w, ⟨l, sorry⟩⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }

set_option timeout 10000000

-- @[simp] lemma remove_subscript_lhs_normalize_cons
--   (t : ι) (r' : free_group (ι × C∞))
--   {A B : set (ι × C∞)}
--   [decidable_pred A] [decidable_pred B]
--   (hA : solver r' A)
--   (hB : solver r' B) :
--   Π (old1 : free_group (ι × C∞))
--   (old2 : P (free_group (ι × C∞))),
--   remove_subscript t (lhs r' (normalize_cons t r' hA hB old1 old2)) =
--     remove_subscript t (old1 * lhs r' old2)
-- | old1 ⟨w, ⟨[], _⟩⟩     := by rw normalize_cons; simp [inl_aut]
-- | old1 ⟨w, ⟨i :: l, _⟩⟩ := begin
--   rw [normalize_cons],
--   split_ifs,
--   { cases h1 : hA old1,
--     { simp [remove_subscript_lhs_normalize_cons, inl_aut_inv, mul_assoc] },
--     { have : i.1.2 = of_add 1, from sorry,
--       simp [remove_subscript_lhs_normalize_cons, mul_assoc, inl_aut_inv,
--         lhs_inl_eq_of_mem _ _ h1, inl_aut, this, h, of_eq_of',
--         lhs_eq_of_mem _ _ h1], } },
--   { cases h2 : hB old1,
--     { simp [remove_subscript_lhs_normalize_cons, inl_aut_inv, mul_assoc] },
--     { have : i.1.2 = of_add 1, from sorry,
--       simp [remove_subscript_lhs_normalize_cons, mul_assoc, inl_aut_inv,
--         lhs_inl_eq_of_mem _ _ h2, inl_aut, this, h, of_eq_of',
--         lhs_eq_of_mem _ _ h2] } },
--   { simp [remove_subscript_lhs_normalize_cons, inl_aut_inv, mul_assoc] },
-- end
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }

noncomputable def normalize_with_subscript_aux
  (t : ι) (r' : free_group (ι × C∞))
  {A B : set (ι × C∞)}
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) :
  Π (w : list (Σ i : ι, C∞)) (hw : coprod.pre.reduced w),
  P (free_group (ι × C∞))
| []       _ := 1
| (i :: l) h := normalize_cons t r' hA hB (of' (i.1, 1) i.2)
  (normalize_with_subscript_aux l (coprod.pre.reduced_of_reduced_cons h))

noncomputable def normalize_with_subscript
  (t : ι) (r' : free_group (ι × C∞))
  {A B : set (ι × C∞)}
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B)
  (w : free_group ι) :
  P (free_group (ι × C∞)) :=
normalize_with_subscript_aux t r' hA hB w.1 w.2

-- lemma remove_subscript_lhs_normalize_with_subscript_aux
--   (t : ι) (r' : free_group (ι × C∞))
--   {A B : set (ι × C∞)}
--   [decidable_pred A] [decidable_pred B]
--   (hA : solver r' A) (hB : solver r' B) :
--   Π (w : list (Σ i : ι, C∞)) (hw : coprod.pre.reduced w),
--   remove_subscript t (lhs r' (normalize_with_subscript_aux t r' hA hB w hw)) = ⟨w, hw⟩
-- | []       _ := by simp [normalize_with_subscript_aux]
-- | (i :: l) _ := begin
--   rw [normalize_with_subscript_aux, remove_subscript_lhs_normalize_cons,
--     monoid_hom.map_mul, remove_subscript_lhs_normalize_with_subscript_aux],
--   simp
-- end

-- @[simp] lemma remove_subscript_lhs_normalize_with_subscript
--   (t : ι) (r' : free_group (ι × C∞)) {A B : set (ι × C∞)}
--   [decidable_pred A] [decidable_pred B]
--   (hA : solver r' A) (hB : solver r' B) (w : free_group ι) :
--   remove_subscript t (lhs r' (normalize_with_subscript t r' hA hB w)) = w :=
-- by cases w; apply remove_subscript_lhs_normalize_with_subscript_aux

-- def exp_sum_eq_zero (t x : ι)
--   (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
--   (cyc_r : free_group ι):
--   solver cyc_r T := λ w,
-- let (c₂, conj_r) := cyclically_conjugate x cyc_r in
-- let r' := (add_subscript t conj_r).left in
-- let (a, b) := min_max_subscript x r' in
-- let p := normalize_with_subscript t r'
--   (hs r' (Icc_prod x a (b * (of_add 1)⁻¹)))
--   (hs r' (Icc_prod x (a * of_add 1) b))
--   w in
-- let T' : set (ι × C∞) :=
--   if t ∈ T
--     then { i : ι × C∞ | i.1 ∈ T }
--     else { i : ι × C∞ | i.1 ∈ T ∧ i.2 = 1 } in
-- let dT' : decidable_pred T' := by dsimp [T']; split_ifs; apply_instance in
-- do np ← @hs r' T' dT' p.right,
-- return (change_r (c₂⁻¹) (P.map (remove_subscript t) sorry (P.trans p np)))
