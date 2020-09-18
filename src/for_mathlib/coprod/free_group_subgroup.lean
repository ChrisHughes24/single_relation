import .free_group group_theory.subgroup

variables {ι : Type*} [decidable_eq ι]

open free_group  subgroup function

lemma mul_aux_mem (S : Π i, subgroup (C∞ )) : ∀ (l₁ l₂ : list (Σ i : ι, C∞ ))
  (h₁ : ∀ a : Σ i : ι, C∞ , a ∈ l₁ → a.2 ∈ S a.1)
  (h₂ : ∀ a : Σ i : ι, C∞ , a ∈ l₂ → a.2 ∈ S a.1)
  {i : ι} {a : C∞ } (ha : (⟨i, a⟩ : Σ i : ι, C∞ ) ∈ coprod.pre.mul_aux l₁ l₂),
  a ∈ S i
| []           l₂      := by simp [coprod.pre.mul_aux]
| (⟨j, b⟩::l₁) []      := begin
    assume h₁ _ i a ha,
    simp only [coprod.pre.mul_aux, list.mem_reverse, list.mem_cons_iff] at ha,
    rcases ha with ⟨rfl, hab⟩ | hia,
    { rw [heq_iff_eq] at hab,
      subst hab,
      exact h₁ ⟨i, a⟩ (list.mem_cons_self _ _) },
    { exact h₁ ⟨i, a⟩ (list.mem_cons_of_mem _ hia) }
  end
| (⟨j, b⟩::l₁) (⟨k, c⟩::l₂) := begin
  assume h₁ h₂ i a ha,
  simp only [coprod.pre.mul_aux] at ha,
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

def blah (S : Π i, subgroup (C∞ )) : subgroup (free_group ι) :=
{ carrier  := { w : free_group ι | ∀ (a : Σ i : ι, C∞ ), a ∈ w.to_list → a.2 ∈ S a.1 },
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

lemma mem_blah (S : Π i, subgroup (C∞ )) (w : free_group ι) :
  w ∈ blah S ↔ ∀ (a : Σ i : ι, C∞ ), a ∈ w.to_list → a.2 ∈ S a.1 := iff.rfl

variable {S : Π i : ι, subgroup C∞}

@[simp] lemma of'_mem_blah_iff {i : ι} {a : C∞ } : of' i a ∈ blah S ↔ a ∈ S i :=
begin
  simp only [mem_blah, of', coprod.to_list_of],
  split_ifs,
  { simp [*, subgroup.one_mem] },
  { simp only [list.mem_singleton],
    split,
    { exact λ h, h ⟨i, a⟩ rfl },
    { assume ha j hj,
      subst j,
      exact ha } }
end

lemma blah_eq_supr : blah S = ⨆ i, (S i).map (of' i) :=
le_antisymm
  (λ w hw, begin
    cases w with l hl,
    induction l with i l ih,
    { simp [subgroup.one_mem] },
    { rw [coprod.cons_eq_of_mul],
      refine subgroup.mul_mem _ _ _,
      { exact (le_supr (λ i, (S i).map begin show C∞  →* free_group ι, from of' i end) i.1 : _)
        (mem_map.2 ⟨i.2, hw _ (list.mem_cons_self _ _), rfl⟩) },
      { exact ih _ (λ j hj, hw _ (list.mem_cons_of_mem _ hj)) } }
  end)
  (supr_le (λ i a ha, begin
    rw [mem_map] at ha,
    rcases ha with ⟨a, ha, rfl⟩,
    simp only [of', coprod.to_list_of, mem_blah],
    split_ifs,
    { simp },
    { simp only [list.mem_singleton],
      assume a ha,
      subst a,
      exact ha }
  end))

lemma range_lift' {G : Type*} [group G] (f : Π i : ι, C∞ →* G) :
  (free_group.lift' f).range = ⨆ i : ι, (f i).range :=
le_antisymm
  begin
    rintros w,
    rw [monoid_hom.mem_range],
    rintros ⟨w, rfl⟩,
    refine free_group.rec_on' w _ _ _,
    { simp [subgroup.one_mem] },
    { assume i n,
      rw [lift'_of'],
      refine le_supr (λ i : ι,(f i).range) i _,
      erw [monoid_hom.mem_range],
      use [n, rfl] },
    { assume i n w ih₁ ih₂,
      simp only [lift'_of', monoid_hom.map_mul] at *,
      exact subgroup.mul_mem _ ih₁ ih₂ }
  end
  (supr_le begin
    assume i w,
    rw [monoid_hom.mem_range],
    rintros ⟨n, rfl⟩,
    rw [monoid_hom.mem_range],
    use of' i n,
    simp,
  end)

/-- `closure_var` is the group closure of a set of variables -/
def closure_var (T : set ι) : subgroup (free_group ι) :=
blah (λ i, ⨆ (h : i ∈ T), ⊤)

instance decidable_blah [Π i : ι, decidable_pred (∈ S i)] : decidable_pred (∈ blah S) :=
λ w, show decidable (∀ (a : Σ i : ι, C∞ ), a ∈ w.to_list → a.2 ∈ S a.1),
  by apply_instance

instance decidable_closure_var (T : set ι) [decidable_pred T] : decidable_pred (∈ closure_var T) :=
λ w, decidable_of_iff (list.all w.to_list (λ i, i.1 ∈ T)) sorry

lemma mem_supr_of_mem {G : Type*} [group G] {ι : Type*} {S : ι → subgroup G} (i : ι) :
  ∀ {x : G}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

lemma range_lift {G : Type*} [group G] (f : ι → G) :
  (free_group.lift f).range = subgroup.closure (set.range f) :=
begin
  simp only [free_group.lift, range_lift', subgroup.range_gpowers_hom,
    gpowers_eq_closure],
  refine le_antisymm _ _,
  { exact supr_le (λ x, closure_mono (λ y, by simp {contextual := tt})) },
  { refine (closure_le _).2 _,
    rw [set.range_eq_Union],
    refine set.Union_subset (λ i x hx, _),
    rw [subgroup.mem_coe],
    exact mem_supr_of_mem i (subgroup.subset_closure hx) }
end
