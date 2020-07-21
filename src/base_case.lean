import for_mathlib.coproduct .functor

variables {ι : Type} [decidable_eq ι]

noncomputable theory

open multiplicative free_group P semidirect_product

@[simp] lemma gpowers_hom_apply {G : Type*} [group G] (x : G) (y : C∞) :
  gpowers_hom G x y = x ^ y.to_add := rfl

def pow_single_cons (r₁ : ι) (r₂ : C∞) (i : ι) (n : C∞) :
  P (free_group ι) → P (free_group ι)
| ⟨w, ⟨[], _⟩⟩ :=
  if i = r₁ ∧ to_add r₂ ∣ to_add n
  then ⟨of' (1 : free_group ι) (of_add (to_add n / to_add r₂)) * w, 1⟩
  else ⟨mul_free (of' i n) w, ⟨[⟨i, n⟩], sorry⟩⟩
| ⟨w, ⟨(j::l), _⟩⟩ :=
  if i = r₁
  then let x := to_add n + to_add j.2 in
    if j.1 = r₁ ∧ to_add r₂ ∣ x
    then ⟨mul_free (of' i n) w * of' (1 : free_group ι) (of_add (x / (to_add r₂))), ⟨l, sorry⟩⟩
    else if (to_add r₂ : ℤ) ∣ to_add n
      then ⟨mul_free (of' i n) w * of' (1 : free_group ι) (of_add (to_add n / to_add r₂)),
        ⟨(j :: l), sorry⟩⟩
      else ⟨mul_free (of' i n) w, ⟨⟨i, n⟩ :: j :: l, sorry⟩⟩
  else ⟨mul_free (of' i n) w, ⟨⟨i, n⟩ :: j :: l, sorry⟩⟩

/--  -/
noncomputable def pow_single (r₁ : ι) (r₂ : C∞) : free_group ι → P (free_group ι)
| ⟨[], h⟩ := ⟨1, ⟨[], h⟩⟩
| ⟨(i::l), _⟩ := -- inr (of' i.1 i.2⁻¹) *
  pow_single_cons r₁ r₂ i.1 i.2
  (pow_single (⟨l, sorry⟩))
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }


@[simp] lemma lhs_pow_single_cons (r₁ : ι) (r₂ : C∞) (hr₂ : to_add r₂ ≠ 0) (i : ι) (n : C∞) :
  Π (x : P (free_group ι)), lhs (of' r₁ r₂) (pow_single_cons r₁ r₂ i n x) =
    of' i n * lhs (of' r₁ r₂) x
| ⟨w, ⟨[], _⟩⟩ := begin
  rw [pow_single_cons],
  split_ifs,
  { clear_aux_decl,
    rcases h with ⟨rfl, m, hm⟩,
    simp [lhs_inl, free_group.lift, gpowers_hom_apply],
    simp only [of'_eq_pow, ← gpow_add, ← gpow_neg, ← gpow_mul,
      int.div_eq_of_eq_mul_right hr₂ hm],
    rw hm },
  { simp [inl_aut] }
end
| ⟨w, ⟨(j::l), _⟩⟩ := begin
  clear_aux_decl,
  rw [pow_single_cons],
  dsimp only,
  split_ifs,
  { subst r₁,
    rcases h_1 with ⟨rfl, m, hm⟩,
    rw [int.div_eq_of_eq_mul_right hr₂ hm],
    rw [← eq_sub_iff_add_eq] at hm,
    simp [lhs_inl, free_group.lift, mul_assoc, gpowers_hom_apply, inl_aut, hm],
    simp only [of'_eq_pow, ← gpow_add, ← gpow_neg, ← gpow_mul, ← mul_assoc, hm],
    simp },
  { subst r₁,
    rcases h_2 with ⟨m, hm⟩,
    rw [int.div_eq_of_eq_mul_right hr₂ hm],
    simp [lhs_inl, free_group.lift, mul_assoc, gpowers_hom_apply, inl_aut, hm],
    simp only [of'_eq_pow, ← gpow_add, ← gpow_neg, ← gpow_mul, ← mul_assoc, hm],
    simp },
  { simp [inl_aut_inv, inl_aut, mul_assoc] },
  { simp [inl_aut_inv, inl_aut, mul_assoc] }
end

lemma lhs_pow_single (r₁ : ι) (r₂ : C∞) (hr₂ : to_add r₂ ≠ 0) : ∀ x : free_group ι,
  lhs (of' r₁ r₂) (pow_single r₁ r₂ x) = x
| ⟨[], h⟩     := by rw [pow_single]; simp
| ⟨(i::l), _⟩ :=by rw [pow_single, lhs_pow_single_cons, lhs_pow_single];
    simp [inl_aut, inl_aut_inv, mul_assoc, hr₂]
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }