import .basic group_theory.subgroup

variables {ι : Type*} {G : ι → Type*}
variables [decidable_eq ι] [Π i, decidable_eq (G i)]
variables [Π i, group (G i)]

open coprod  subgroup function

lemma mul_aux_mem (S : Π i, subgroup (G i)) : ∀ (l₁ l₂ : list (Σ i, G i))
  (h₁ : ∀ a : Σ i, G i, a ∈ l₁ → a.2 ∈ S a.1)
  (h₂ : ∀ a : Σ i, G i, a ∈ l₂ → a.2 ∈ S a.1)
  {i : ι} {a : G i} (ha : (⟨i, a⟩ : Σ i, G i) ∈ pre.mul_aux l₁ l₂),
  a ∈ S i
| []           l₂      := by simp [pre.mul_aux]
| (⟨j, b⟩::l₁) []      := begin
    assume h₁ _ i a ha,
    simp only [pre.mul_aux, list.mem_reverse, list.mem_cons_iff] at ha,
    rcases ha with ⟨rfl, hab⟩ | hia,
    { rw [heq_iff_eq] at hab,
      subst hab,
      exact h₁ ⟨i, a⟩ (list.mem_cons_self _ _) },
    { exact h₁ ⟨i, a⟩ (list.mem_cons_of_mem _ hia) }
  end
| (⟨j, b⟩::l₁) (⟨k, c⟩::l₂) := begin
  assume h₁ h₂ i a ha,
  simp only [pre.mul_aux] at ha,
  split_ifs at ha,
  { exact mul_aux_mem _ _
      (λ d hd, h₁ d (list.mem_cons_of_mem _ hd))
      (λ d hd, h₂ d (list.mem_cons_of_mem _ hd))
      ha },
  { dsimp at h,
    subst j,
    simp only [list.reverse_core_eq, list.mem_append, list.mem_cons_iff,
      list.mem_reverse, cast_eq] at ha,
    simp only [cast_eq] at *,
    rcases ha with ha | ⟨rfl, h, h⟩ | ha,
    { exact h₁ ⟨i, a⟩ (list.mem_cons_of_mem _ ha) },
    { exact subgroup.mul_mem _
        (h₁ ⟨i, b⟩ (list.mem_cons_self _ _))
        (h₂ ⟨i, c⟩ (list.mem_cons_self _ _)) },
    { exact h₂ ⟨i, a⟩ (list.mem_cons_of_mem _ ha) } },
  { clear_aux_decl,
    simp only [list.reverse_core_eq, list.mem_append, list.mem_cons_iff,
      list.mem_reverse] at ha,
    rcases ha with ha | ⟨rfl, hab⟩ | ⟨rfl, hab⟩ | ha,
    { exact h₁ ⟨i, a⟩ (list.mem_cons_of_mem _ ha) },
    { rw [heq_iff_eq] at hab,
      subst hab,
      exact h₁ ⟨i, a⟩ (list.mem_cons_self _ _) },
    { rw [heq_iff_eq] at hab,
      subst hab,
      exact h₂ ⟨i, a⟩ (list.mem_cons_self _ _) },
    { exact h₂ ⟨i, a⟩ (list.mem_cons_of_mem _ ha) } }
end

def blah (S : Π i, subgroup (G i)) : subgroup (coprod G) :=
{ carrier  := { w : coprod G | ∀ (a : Σ i, G i), a ∈ w.to_list → a.2 ∈ S a.1 },
  one_mem' := λ a h, h.elim,
  mul_mem' := begin
    rintros ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ h₁ h₂ ⟨i, a⟩ h,
    exact mul_aux_mem S l₁.reverse l₂ (by simpa using h₁) (by simpa using h₂) h
  end,
  inv_mem' := begin
    rintros ⟨l, hl⟩ h i hi,
    dsimp at *,
    replace hi : i ∈ (l.map _).reverse := hi,
    rw [← inv_mem_iff],
    simp at hi,
    rcases hi with ⟨j, a, ha, rfl⟩,
    simp,
    exact h _ ha
  end }

lemma mem_blah (S : Π i, subgroup (G i)) (w : coprod G) :
  w ∈ blah S ↔ ∀ (a : Σ i, G i), a ∈ w.to_list → a.2 ∈ S a.1 := iff.rfl

variable {S : Π i, subgroup (G i)}

@[simp] lemma of_mem_blah_iff {i : ι} {a : G i} : of i a ∈ blah S ↔ a ∈ S i :=
begin
  simp only [mem_blah, to_list_of],
  split_ifs,
  { simp [*, subgroup.one_mem] },
  { simp only [list.mem_singleton],
    split,
    { exact λ h, h ⟨i, a⟩ rfl },
    { assume ha j hj,
      subst j,
      exact ha } }
end

lemma blah_eq_supr : blah S = ⨆ i, (S i).map (of i) :=
le_antisymm
  (λ w hw, begin
    cases w with l hl,
    induction l with i l ih,
    { simp [subgroup.one_mem] },
    { rw [cons_eq_of_mul],
      refine subgroup.mul_mem _ _ _,
      { exact (le_supr (λ i, (S i).map begin show G i →* coprod G, from of i end) i.1 : _)
        (mem_map.2 ⟨i.2, hw _ (list.mem_cons_self _ _), rfl⟩) },
      { exact ih _ (λ j hj, hw _ (list.mem_cons_of_mem _ hj)) } }
  end)
  (supr_le (λ i a ha, begin
    rw [mem_map] at ha,
    rcases ha with ⟨a, ha, rfl⟩,
    simp only [to_list_of, mem_blah],
    split_ifs,
    { simp },
    { simp only [list.mem_singleton],
      assume a ha,
      subst a,
      exact ha }
  end))
