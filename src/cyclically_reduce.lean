import for_mathlib.coprod.free_group

variables {ι : Type} [decidable_eq ι]

open free_group mul_aut

@[simp] lemma init_eq (l : list (Σ i : ι, C∞)) --(hl : reduced l)
  (hl' : l ≠ []) : @eq (free_group ι) ⟨l.init, sorry⟩ (⟨l, sorry⟩ *
    of' (l.last hl').1 (l.last hl').2⁻¹) := sorry

/-- given a word `r` returns a pair `(g, r')` such that `r'` is cyclically reduced
  and `g * r * g⁻¹ = r'` -/
noncomputable def cyclically_reduce : free_group ι → free_group ι × free_group ι
| ⟨[], _⟩      := (1, 1)
| ⟨[i], h⟩     := (1, ⟨[i], h⟩)
| ⟨i::j::l, h⟩ :=
  let k := (j :: l : list _).last (list.cons_ne_nil _ _) in
  if i.1 = k.1
  then
    let z := k.2 * i.2 in
    if z = 1
    then
      let init : free_group ι := ⟨(j :: l : list _).init, sorry⟩ in
      let w' := cyclically_reduce init in
      (w'.1 * of' k.1 k.2, w'.2)
    else
      (of' k.1 k.2, ⟨⟨k.1, z⟩ ::  (j :: l : list _).init, sorry⟩)
  else (1, ⟨i::j::l, h⟩)
using_well_founded {rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩],
  dec_tac := `[trivial]}

lemma conj_cyclically_reduce : ∀ (r : free_group ι),
  conj (cyclically_reduce r).1 r = (cyclically_reduce r).2
| ⟨[], _⟩      := by rw [cyclically_reduce]; simp
| ⟨[i], _⟩     := by rw [cyclically_reduce]; simp
| ⟨i::j::l, _⟩ := begin
  simp only [cyclically_reduce],
  split_ifs,
  { cases i,
    dsimp only at h h_1,
    rw [mul_eq_one_iff_inv_eq, eq_comm] at h_1,
    conv_rhs { rw [← conj_cyclically_reduce] },
    simp * },
  { simp [h, mul_assoc] },
  { simp }
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩],
  dec_tac := `[trivial]}


