import .functor
import .for_mathlib.coprod.free_group_subgroup
import neat.initial
import data.nat.digits
/-!
# The base case of the `group_thingy` tactic

## Main definitions
The only definition used outside of this file is `base_case_solver`.
`base_case_solver T r₁ r₂` solves the word problem for the relation `of' r₁ r₂`, returning
a normalized word in `T` when possible, and `none` otherwise
-/
variables {ι : Type} [decidable_eq ι]

open multiplicative free_group P semidirect_product

@[simp] lemma gpowers_hom_apply {G : Type*} [group G] (x : G) (y : C∞) :
  gpowers_hom G x y = x ^ y.to_add := rfl

def base_case'_cons (r₁ : ι) (r₂ : C∞) (i : ι) (n : C∞) :
  P (free_group ι) → P (free_group ι)
| ⟨w, ⟨[], _⟩⟩ :=
  if i = r₁ ∧ to_add r₂ ∣ to_add n
  then ⟨of' (1 : free_group ι) (of_add (to_add n / to_add r₂)) * w, 1⟩
  else ⟨mul_free (of' i n) w, ⟨[⟨i, n⟩], sorry⟩⟩
| ⟨w, ⟨(j::l), h⟩⟩ :=
  if i = r₁
  then let x := to_add n + to_add j.2 in
    if j.1 = r₁ ∧ to_add r₂ ∣ x
    then ⟨mul_free (of' i n) w * of' (1 : free_group ι) (of_add (x / (to_add r₂))), ⟨l, sorry⟩⟩
    else if (to_add r₂ : ℤ) ∣ to_add n
      then ⟨mul_free (of' i n) w * of' (1 : free_group ι) (of_add (to_add n / to_add r₂)),
        ⟨(j :: l), h⟩⟩
      else ⟨mul_free (of' i n) w, of' i n * ⟨j :: l, h⟩⟩
  else ⟨mul_free (of' i n) w, of' i n * ⟨j :: l, h⟩⟩

def base_case' (r₁ : ι) (r₂ : C∞) : free_group ι → P (free_group ι)
| ⟨[], h⟩ := ⟨1, ⟨[], h⟩⟩
| ⟨(i::l), h⟩ :=
  base_case'_cons r₁ r₂ i.1 i.2 $ base_case' ⟨l, coprod.pre.reduced_of_reduced_cons h⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }

def base_case'_solver (T : set ι) [decidable_pred T] (r₁ : ι) (r₂ : C∞) : solver (of' r₁ r₂) T :=
λ w, let p := base_case' r₁ r₂ w in
if p.right ∈ closure_var T
  then some p
  else none

/-- `base_case_core` takes a word `l₁` in the free_group as a `list (Σ i : ι, C∞)`
and a normalized word with proof `p` as a `P (free_group ι)`.
It returns a normalized version `reverse l₁ * p`, reduced modulo `of' r₁ r₂`  -/
@[inline] def base_case_core (r₁ : ι) (r₂ : C∞) : list (Σ i : ι, C∞) →
  P (free_group ι) → P (free_group ι)
| []     p := p
| (i::l₁)  ⟨p, ⟨[], _⟩⟩ :=
  if i.1 = r₁
    then if to_add r₂ ∣ i.2
      then let q := to_add i.2 / to_add r₂ in
        base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, 1⟩)
      else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, 1⟩)
    else base_case_core l₁ (inr (of' i.1 i.2) * inl p)
| (i::l₁) ⟨p, ⟨j::l₂, _⟩⟩ :=
  if i.1 = r₁
    then if j.1 = r₁
      then
        let x := to_add i.2 + to_add j.2 in
        if to_add r₂ ∣ x
        then base_case_core l₁ (inl (of' (1 : free_group ι) (of_add (to_add x / to_add r₂))) *
          inr (of' j.1 j.2⁻¹) * ⟨p, ⟨j::l₂, sorry⟩⟩)
        else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
      else if to_add r₂ ∣ i.2
        then let q := to_add i.2 / to_add r₂ in
          base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, ⟨j::l₂, sorry⟩⟩)
        else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
    else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)

-- def normalize_single (r₁ : ι) (r₂ : C∞) (i : ι) (n : C∞) : P (free_group ι) :=
-- if i = r₁ ∧ to_add r₂ ∣ to_add n
--   then ⟨of' 1 (of_add (to_add n / to_add r₂)), 1⟩
--   else ⟨1, of' i n⟩

-- def mul_left (r₁ : ι) (r₂ : C∞) (i : ι) (n : C∞) :
--   P (free_group ι) → P (free_group ι)
-- | ⟨p, ⟨[], _⟩⟩ := normalize_single r₁ r₂ i n * inl p
-- | ⟨p, ⟨(j::l), _⟩⟩ :=
-- if i = j.1
--   then _
--   else _

-- -- @[inline] def base_case_core₂ (r₁ : ι) (r₂ : C∞) : list (Σ i : ι, C∞) →
-- --   P (free_group ι) → P (free_group ι)
-- -- | []     p := p
-- -- | (i::l₁)  ⟨p, ⟨[], _⟩⟩ :=
-- --   if i.1 = r₁
-- --     then if to_add r₂ ∣ i.2
-- --       then let q := to_add i.2 / to_add r₂ in
-- --         base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, 1⟩)
-- --       else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, 1⟩)
-- --     else base_case_core l₁ (inr (of' i.1 i.2) * inl p)
-- -- | (i::l₁) ⟨p, ⟨j::l₂, _⟩⟩ :=
-- --   if i.1 = r₁
-- --     then if j.1 = r₁
-- --       then
-- --         let x := to_add i.2 + to_add j.2 in
-- --         if to_add r₂ ∣ x
-- --         then base_case_core l₁ (inl (of' (1 : free_group ι) (of_add (to_add x / to_add r₂))) *
-- --           inr (of' j.1 j.2⁻¹) * ⟨p, ⟨j::l₂, sorry⟩⟩)
-- --         else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
-- --       else if to_add r₂ ∣ i.2
-- --         then let q := to_add i.2 / to_add r₂ in
-- --           base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, ⟨j::l₂, sorry⟩⟩)
-- --         else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
-- --     else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)

/-- `base_case` reduces a word `w` in the `free_group ι` modulo `of' r₁ r₂` -/
@[inline] def base_case (r₁ : ι) (r₂ : C∞) (w : free_group ι) : P (free_group ι) :=
base_case_core r₁ r₂ w.to_list.reverse 1

/-- `base_case_solver T r₁ r₂` solves the word problem for the relation `of' r₁ r₂`, returning
a normalized word in `T` when possible, and `none` otherwise -/
@[inline] def base_case_solver (T : set ι) [decidable_pred T] (r₁ : ι) (r₂ : C∞) : solver (of' r₁ r₂) T :=
λ w, let p := base_case r₁ r₂ w in
if p.right ∈ closure_var T
  then some p
  else none

#eval --(of' 0 (of_add 2))
  P.lhs (of' 0 (of_add 2)) ((base_case 0 (of_add 2) ((of 1)⁻¹ *of 0^(-2 : ℤ) * (of 1)⁻¹ * of 0 ^2* (of 1)^(-2 : ℤ) * (of 0)^2)))
#eval ((base_case 1 (of_add 1) ((of 0)⁻¹ * of 1 * of 0 ^ 2 * (of 1) * (of 0)⁻¹)).left)
#eval ((base_case' 0 (of_add 2) (of 1 *of 0^2 * (of 1) * of 0 ^2* (of 1)^(-2 : ℤ) * (of 0)^2)).left)
#eval ((base_case' 1 (of_add 1) ((of 0)⁻¹ * of 1 * of 0 ^ 2 * (of 1) * (of 0)⁻¹)).left)

@[simp] lemma lhs_base_case'_cons (r₁ : ι) (r₂ : C∞) (hr₂ : to_add r₂ ≠ 0) (i : ι) (n : C∞) :
  Π (x : P (free_group ι)), lhs (of' r₁ r₂) (base_case'_cons r₁ r₂ i n x) =
    of' i n * lhs (of' r₁ r₂) x
| ⟨w, ⟨[], _⟩⟩ := begin
  rw [base_case'_cons],
  split_ifs,
  { clear_aux_decl,
    rcases h with ⟨rfl, m, hm⟩,
    simp [lhs_inl, free_group.lift, gpowers_hom_apply],
    simp only [of'_eq_of_pow, ← gpow_add, ← gpow_neg, ← gpow_mul,
      int.div_eq_of_eq_mul_right hr₂ hm],
    rw hm },
  { simp [inl_aut] }
end
| ⟨w, ⟨(j::l), _⟩⟩ := begin
  clear_aux_decl,
  rw [base_case'_cons],
  dsimp only,
  split_ifs,
  { subst r₁,
    rcases h_1 with ⟨rfl, m, hm⟩,
    rw [int.div_eq_of_eq_mul_right hr₂ hm],
    rw [← eq_sub_iff_add_eq] at hm,
    simp [lhs_inl, free_group.lift, mul_assoc, gpowers_hom_apply, inl_aut, hm],
    simp only [of'_eq_of_pow, ← gpow_add, ← gpow_neg, ← gpow_mul, ← mul_assoc, hm],
    simp },
  { subst r₁,
    rcases h_2 with ⟨m, hm⟩,
    rw [int.div_eq_of_eq_mul_right hr₂ hm],
    simp [lhs_inl, free_group.lift, mul_assoc, gpowers_hom_apply, inl_aut, hm],
    simp only [of'_eq_of_pow, ← gpow_add, ← gpow_neg, ← gpow_mul, ← mul_assoc, hm],
    simp },
  { simp [inl_aut_inv, inl_aut, mul_assoc] },
  { simp [inl_aut_inv, inl_aut, mul_assoc] }
end

lemma lhs_base_case' (r₁ : ι) (r₂ : C∞) (hr₂ : to_add r₂ ≠ 0) :
  ∀ x : free_group ι, lhs (of' r₁ r₂) (base_case' r₁ r₂ x) = x
| ⟨[], h⟩     := by rw [base_case']; simp
| ⟨(i::l), _⟩ := by rw [base_case', lhs_base_case'_cons, lhs_base_case'];
    simp [inl_aut, inl_aut_inv, mul_assoc, hr₂]
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }