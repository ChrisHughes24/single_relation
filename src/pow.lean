import for_mathlib.coprod.free_group_subgroup
import .functor
import .initial

variables {ι : Type} {M : ι → Type}
variables [decidable_eq ι] [Π i, decidable_eq (M i)]
variables [Π i, monoid (M i)]

open list

section partial_prod

open coprod

/-- `partial_prod l` returns the list of products of final segments of `l`.
  e.g. `partial_prod [a, b, c]` = `[a * b * c, b * c, c]`  -/
def list.partial_prod {M : Type*} [monoid M] : list M → list M
| []     := []
| (a::l) := (a::l : list _).prod :: list.partial_prod l

lemma prod_mem_partial_prod {M : Type*} [monoid M] (l : list M) :
  l = [] ∨ l.prod ∈ l.partial_prod :=
by cases l; simp [list.partial_prod]

lemma partial_prod_append {M : Type*} [monoid M] (l₁ l₂ : list M) :
  (l₁ ++ l₂).partial_prod = l₁.partial_prod.map (* l₂.prod) ++ l₂.partial_prod :=
by induction l₁; simp [list.partial_prod, *, mul_assoc]

def list.partial_prod' {M : Type*} [monoid M] : list M → list M
| []     := [1]
| (a::l) := (a::l : list _).prod :: list.partial_prod' l

lemma partial_prod'_eq_partial_prod_append {M : Type*} [monoid M] (l : list M) :
  l.partial_prod' = l.partial_prod ++ [1] :=
by induction l; simp [*, list.partial_prod, list.partial_prod'] at *

def partial_prod'_concat {M : Type*} [monoid M] (l : list M) (a : M) :
  (l ++ [a]).partial_prod' = l.partial_prod'.map (* a) ++ [1] :=
by induction l; simp [list.partial_prod', mul_assoc, *]

lemma partial_prod'_reverse_inv {G : Type*} [group G] (l : list G) :
  ((l: list _).map has_inv.inv).reverse.partial_prod' =
  (l : list _).partial_prod'.reverse.map (λ x, x * l.prod⁻¹) :=
begin
  induction l with g l ih,
  { simp [list.partial_prod', mul_assoc] },
  { simp [list.partial_prod', partial_prod'_concat, ih,
      function.comp, mul_assoc] }
end

lemma mem_partial_prod_reverse_inv {G : Type*} [group G] {l : list G} {x : G} (hx : x ≠ 1) :
  x ∈ ((l: list _).map has_inv.inv).reverse.partial_prod ↔
    x ∈ (l : list _).partial_prod.map (λ x, x * l.prod⁻¹) ∨ x = l.prod⁻¹ :=
begin
  have := congr_arg ((∈) x) (partial_prod'_reverse_inv l),
  simp only [partial_prod'_eq_partial_prod_append, list.mem_append,
    list.mem_singleton, hx, or_false, list.mem_reverse,
    list.map_reverse, list.map_append] at this,
  rw this,
  simp
end

lemma partial_prod_sublist_aux₁ (i : ι) (a : M i) :
  ∀ (l : list (Σ i, M i)) (hl : pre.reduced l),
  ((of i a * ⟨l, hl⟩).to_list.map (λ i : Σ i, M i, of i.1 i.2)).partial_prod <+
    (of i a * (l.map (λ i : Σ i, M i, of i.1 i.2)).prod) :: (l.map (λ i : Σ i, M i, of i.1 i.2)).partial_prod
| [] hl := by simp [list.partial_prod, to_list_of];
  split_ifs; simp [list.partial_prod]
| (⟨j, b⟩::l) hl := begin
  rw [of_mul_cons],
  split_ifs,
  { simp only [h, monoid_hom.map_one, one_mul, coprod.to_list],
    exact list.sublist_cons _ _ },
  { subst j,
    simp only [coprod.to_list, list.map_cons, list.partial_prod],
    exact list.sublist.trans (list.sublist_cons _ _)
      (list.sublist_cons _ _) },
  { subst j,
    simp only [coprod.to_list, list.map_cons,
      list.partial_prod, list.prod_cons, cast_eq],
    dsimp,
    simp only [monoid_hom.map_mul, mul_assoc],
    apply list.sublist.cons2,
    apply list.sublist_cons },
  { simp only [coprod.to_list, list.map_cons,
      list.partial_prod, list.prod_cons, cast_eq] }
end

lemma lift_eq_map_prod {N : Type*} [monoid N] (f : Π i, M i →* N)
  (w : coprod M) : lift f w = (w.to_list.map (λ i : Σ i, M i, f i.1 i.2)).prod :=
pre.lift_eq_map_prod _ _

@[simp] lemma lift_hom_of : coprod.lift (of : Π i : ι, M i →* coprod M) =
  monoid_hom.id _ :=
coprod.hom_ext (by simp)

@[simp] lemma map_prod_of_eq_self (w : coprod M) :
  (w.to_list.map (λ i : Σ i, M i, of i.1 i.2)).prod = w :=
by rw [← lift_eq_map_prod, lift_hom_of, monoid_hom.id_apply]

lemma partial_prod_sublist_aux₂ (i : ι) (a : M i) (w : coprod M) :
  ((of i a * w).to_list.map (λ i : Σ i, M i, of i.1 i.2)).partial_prod <+
    (of i a * w) :: (w.to_list.map (λ i : Σ i, M i, of i.1 i.2)).partial_prod :=
begin
  cases w with l hl,
  convert partial_prod_sublist_aux₁ i a l hl,
  conv_lhs { rw [← map_prod_of_eq_self ⟨l, hl⟩] },
  refl
end

lemma partial_prod_sublist : ∀ (l : list (Σ i, M i)),
  ((l.map (λ i : Σ i, M i, of i.1 i.2)).prod.to_list.map
    (λ i : Σ i, M i, of i.1 i.2)).partial_prod <+
    (l.map (λ i : Σ i, M i, of i.1 i.2)).partial_prod
| []     := by simp [list.partial_prod]
| [i]    := begin
    simp [list.partial_prod, to_list_of],
    split_ifs;
    simp [list.partial_prod]
  end
| (i::l) := begin
  rw [list.map_cons, list.prod_cons, list.partial_prod],
  apply list.sublist.trans (partial_prod_sublist_aux₂ i.1 i.2 (l.map (λ i : Σ i, M i, of i.1 i.2)).prod),
  simp only [list.prod_cons, map_prod_of_eq_self],
  apply list.sublist.cons2,
  exact partial_prod_sublist _
end

end partial_prod

open free_group

@[reducible] def fprod (l : list (Σ i : ι, C∞)) : free_group ι :=
(l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)).prod

@[reducible] def fpprod (l : list (Σ i : ι, C∞)) : list (free_group ι) :=
(l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)).partial_prod

lemma mem_blah_iff_partial_prod_mem_blah (S : ι → subgroup C∞) (w : free_group ι) :
  (∀ v : free_group ι, v ∈ fpprod w.to_list → v ∈ blah S)
  ↔ w ∈ blah S :=
begin
  cases w with l hl,
  induction l with i l ih,
  { simp [list.partial_prod, subgroup.one_mem, fpprod] },
  { simp only [list.partial_prod, coprod.to_list_mk, list.map_cons,
      list.mem_cons_iff, list.prod_cons],
    split,
    { assume hv,
      refine hv _ (or.inl _),
      rw [coprod.cons_eq_of_mul, ← map_prod_of_eq_self
        ⟨l, coprod.pre.reduced_of_reduced_cons hl⟩],
      simp [of'] },
    { intros h v hv,
      rcases hv with rfl | hv,
      { convert h,
        rw [← map_prod_of_eq_self ⟨i :: l, hl⟩, coprod.to_list],
        simp [of'] },
      { refine (ih (coprod.pre.reduced_of_reduced_cons hl)).2 _ _ hv,
        { assume j hj, exact h j (list.mem_cons_of_mem _ hj) } } } }
end

def pow_single (t : ι) (n : C∞) : free_group ι →* free_group ι :=
free_group.lift (λ i, if t = i then free_group.of' i n else free_group.of i)

lemma exp_sum_comp_pow_single (t : ι) (n : C∞) :
  (exp_sum t).comp (pow_single t n) = (gpowers_hom _ n).comp (exp_sum t) :=
hom_ext (λ i, begin
  simp [pow_single, exp_sum, of_eq_of', free_group.lift],
  split_ifs,
  { simp [*, gpowers_hom] },
  { simp [*, gpowers_hom] }
end)

lemma range_pow_single (t : ι) (n : C∞) : (pow_single t n).range =
  blah (λ i : ι, show subgroup C∞, from ⨅ (h : t = i), subgroup.gpowers n) :=
begin
  rw [blah_eq_supr, pow_single, range_lift],
  refine le_antisymm
    ((subgroup.closure_le _).2 (set.range_subset_iff.2 _))
    (supr_le _),
  { assume i,
    have := le_supr (λ i : ι, show subgroup (free_group ι), from subgroup.map (of' i)
      (show subgroup C∞, from ⨅ (h : t = i), subgroup.gpowers n)) i,
    rw [subgroup.le_def] at this,
    refine this _,
    split_ifs,
    { subst i,
      exact subgroup.mem_map.2 ⟨_, by simp, rfl⟩ },
    { exact subgroup.mem_map.2 ⟨multiplicative.of_add 1, by simp [h], rfl⟩ } },
  { assume i,
    refine subgroup.map_le_iff_le_comap.2 (λ m hm, _),
    by_cases h : t = i,
    { rw [h, eq_self_iff_true, infi_true] at hm,
      rcases hm with ⟨k, rfl⟩,
      refine subgroup.gpow_mem _ (subgroup.mem_comap.2 _) _,
      refine subgroup.subset_closure (set.mem_range.2 ⟨i, _⟩),
      simp * },
    { refine subgroup.mem_comap.2 _,
      rw [of'_eq_of_pow],
      refine subgroup.gpow_mem _ _ _,
      refine subgroup.subset_closure (set.mem_range.2 ⟨i, _⟩),
      simp * } }
end

open multiplicative

def eliminate_t (t : ι) (n : C∞) : list (Σ i : ι, C∞) → list (Σ i : option ι, C∞) × C∞
| []          := ([], 1)
| (i::l) :=
let x := eliminate_t l in
if t = i.1
  then if n.to_add ∣ to_add i.2 + to_add x.2
    then (⟨none, of_add ((to_add i.2 + to_add x.2) / n.to_add)⟩ ::
      ⟨some i.1, x.2⁻¹⟩ :: x.1, 1)
    else (⟨some i.1, i.2⟩ :: x.1, i.2 * x.2)
  else (⟨some i.1, i.2⟩ :: x.1, x.2)

lemma eliminate_t_snd (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
  (eliminate_t t n l).2 = exp_sum (some t) (fprod (eliminate_t t n l).1) :=
begin
  induction l,
  { simp [eliminate_t, fprod] },
  { simp only [eliminate_t, exp_sum, l_ih],
    split_ifs at *; simp [*, fprod] }
end

lemma eliminate_t_snd_eq_one (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
  to_add n ∣ (eliminate_t t n l).snd.to_add → (eliminate_t t n l).snd = 1 :=
begin
  induction l with i l ih,
  { simp [eliminate_t] },
  { cases i with i a,
    dsimp only [eliminate_t],
    split_ifs; finish }
end

lemma eliminate_t_exp_sum_eq_one (t : ι) (n : C∞) (l : list (Σ i : ι, C∞))
  (w : free_group (option ι))
  (hw : w ∈ fpprod (eliminate_t t n l).1)
  (hdvd : to_add n ∣ (exp_sum (some t) w).to_add) :
  exp_sum (some t) w = 1 :=
begin
  induction l with i l ih generalizing w,
  { simp [*, list.partial_prod, eliminate_t, fpprod] at * },
  { cases i with i a,
    dsimp only [eliminate_t, fpprod] at hw,
    split_ifs at hw,
    { subst h,
      rw [list.map_cons, list.partial_prod, list.map_cons, list.partial_prod,
        list.mem_cons_iff, list.mem_cons_iff] at hw,
      rcases hw with rfl | rfl| hw,
      { simp [eliminate_t_snd] },
      { simp [eliminate_t_snd] },
      { exact ih _ hw hdvd } },
    { subst h,
      rw [list.map_cons, list.partial_prod, list.mem_cons_iff] at hw,
      rcases hw with rfl | hw,
      { simp [eliminate_t_snd, *] at * },
      { exact ih _ hw hdvd } },
    { rw [list.map_cons, list.partial_prod, list.mem_cons_iff] at hw,
      rcases hw with rfl | hw,
      { simp [eliminate_t_snd, h],
        cases prod_mem_partial_prod ((eliminate_t t n l).1.map
            (λ i : Σ i : option ι, C∞, of' i.1 i.2)) with he he,
        { rw he, simp [subgroup.one_mem] },
        { refine ih _ he _,
          simpa [list.map_cons, h] using hdvd } },
      { exact ih _ hw hdvd } } }
end

lemma prod_eliminate_t (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) (hn : n ≠ 1) :
  lift (λ i : option ι, i.elim (of' t n) of) (fprod (eliminate_t t n l).1) = fprod l :=
begin
  dsimp only [fprod] at *,
  induction l with  i l ih,
  { simp [eliminate_t] },
  { rw [eliminate_t],
    split_ifs,
    { cases h_1 with k hk,
      rw [int.div_eq_of_eq_mul_right (show n.to_add ≠ 0, from hn) hk, list.map_cons, list.map_cons,
        list.map_cons, list.prod_cons, list.prod_cons, list.prod_cons, ← ih],
      simp only [of'_eq_of_pow, monoid_hom.map_gpow, h, monoid_hom.map_list_prod,
        function.comp, lift_of, option.elim, monoid_hom.map_mul,
        to_add_of_add, monoid_hom.map_inv, list.map_map, ← mul_assoc,
        ← gpow_add, ← gpow_neg, ← gpow_mul, ← hk],
      simp },
    { rw [list.map_cons, list.prod_cons, monoid_hom.map_mul, ih],
      simp [of'_eq_of_pow, monoid_hom.map_gpow] },
    { rw [list.map_cons, list.prod_cons, monoid_hom.map_mul, ih],
      simp [of'_eq_of_pow, monoid_hom.map_gpow] } }
end

lemma exp_sum_eq_one_of_mem_closure_var {t : ι} {w : free_group ι} {s : set ι}
  (hw : w ∈ closure_var s) (his : t ∉ s) : exp_sum t w = 1 :=
begin
  cases w with l hl,
  induction l with i l ih,
  { simp },
  { rw [cons_eq_of'_mul, monoid_hom.map_mul, exp_sum_of'],
    have := hw i (list.mem_cons_self _ _),
    have hit : t ≠ i.1,
    { assume hit,
      subst hit,
      have := hl.2 i (list.mem_cons_self _ _),
      simp * at * },
    rw [if_neg hit, one_mul],
    exact ih (coprod.pre.reduced_of_reduced_cons _)
      (λ i hi, hw _ (list.mem_cons_of_mem _ hi)) }
end

lemma mem_closure_var_of_forall_exp_sum_eq_one_aux {t : ι} {l : list (Σ i : ι, C∞)}
  (h : ∀ w, w ∈ fpprod l → exp_sum t w = 1) : fprod l ∈ closure_var {i | t ≠ i} :=
begin
  induction l with i l ih,
  { simp [subgroup.one_mem, fprod] },
  { rw [fprod, list.map_cons, list.prod_cons],
    simp only [list.partial_prod, list.map_cons, fpprod] at h,
    have := h _ (list.mem_cons_self _ _),
    simp at this,
    refine subgroup.mul_mem _ _ _,
    { split_ifs at this,
      { cases prod_mem_partial_prod (l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)) with he he,
        { rw he at this,
          simp [*, subgroup.one_mem] at * },
        { rw [h _ (list.mem_cons_of_mem _ he), mul_one] at this,
          simp [this, subgroup.one_mem] } },
      { rw [closure_var, of'_mem_blah_iff],
        simp [h_1] } },
    { exact ih (λ w hw, h w (list.mem_cons_of_mem _ hw)) } }
end

lemma mem_closure_var_of_forall_exp_sum_eq_one {t : ι} {w : free_group ι}
  (h : ∀ v, v ∈ fpprod w.to_list → exp_sum t v = 1) : w ∈ closure_var {i | t ≠ i} :=
begin
  convert mem_closure_var_of_forall_exp_sum_eq_one_aux h,
  simp only [of', map_prod_of_eq_self, fprod]
end

lemma partial_prod_mem_blah {S : ι → subgroup C∞} {w v : free_group ι}
  (hv : v ∈ fpprod w.to_list) (hw : w ∈ blah S) : v ∈ blah S :=
begin
  cases w with l hl,
  induction l with i l ih,
  { simp [*, fpprod, list.partial_prod] at * },
  { rw [fpprod, coprod.to_list, list.map_cons, list.partial_prod, list.mem_cons_iff] at hv,
    rcases hv with rfl | hv,
    { erw [list.prod_cons, map_prod_of_eq_self ⟨l, coprod.pre.reduced_of_reduced_cons hl⟩],
      refine subgroup.mul_mem _
        (by simp [of'_mem_blah_iff, hw _ (list.mem_cons_self  _ _)])
        (λ i hi, hw _ (list.mem_cons_of_mem _ hi)) },
    { exact ih (coprod.pre.reduced_of_reduced_cons hl) hv
        (λ i hi, hw _ (list.mem_cons_of_mem _ hi)) } }
end

lemma append_exp_sum_eq_one {n : C∞} {t : ι} {l₁ : list (Σ i : ι, C∞)} {r : free_group ι}
  (h₁ : r ∈ closure_var {i | i ≠ t})
  (h₂ : ∀ v, v ∈ fpprod l₁ → n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1) :
  ∀ v ∈ fpprod (l₁ ++ r.to_list), n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1 :=
begin
  assume v hv hn,
  simp only [fpprod, partial_prod_append, list.map_append, list.mem_append] at hv,
  cases hv with hv hv,
  { rcases list.mem_map.1 hv with ⟨w, hw, rfl⟩,
    { erw [monoid_hom.map_mul, map_prod_of_eq_self,
        exp_sum_eq_one_of_mem_closure_var h₁ (by simp), mul_one] at ⊢ hn,
      rw [h₂ _ hw hn] } },
  { exact exp_sum_eq_one_of_mem_closure_var (partial_prod_mem_blah hv h₁) (by simp) }
end

lemma exp_sum_append_subset {t : ι} {l : list (Σ i : ι, C∞)} {r : free_group ι}
  (h₁ : r ∈ closure_var {i | i ≠ t}) :
  ∀ v ∈ fpprod ((l.map (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse ++ r.to_list ++ l),
    exp_sum t v ≠ 1 → (∃ w ∈ fpprod l, exp_sum t v = exp_sum t w) :=
begin
  assume v hv hv1,
  simp only [fpprod, partial_prod_append, function.comp,
    list.map_append, list.mem_append, or.assoc] at hv,
  rw [← fpprod, ← fpprod, ← fpprod, ← fprod, ← fprod] at hv,
  rcases hv with hv | hv | hv,
  { rw [list.map_map, list.mem_map] at hv,
    rcases hv with ⟨w, hw, rfl⟩,
    have hw' : w ∈ ((l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)).map has_inv.inv).reverse.partial_prod,
    { simpa [fpprod, list.map_map, function.comp] using hw },
    simp only [monoid_hom.map_mul],
    erw [fprod, map_prod_of_eq_self, exp_sum_eq_one_of_mem_closure_var h₁ (not_not.2 rfl),
      mul_one],
    by_cases hw1 : w = 1,
    { subst hw1,
      use [fprod l],
      rcases prod_mem_partial_prod (l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)) with hl | hl,
      { simp [*, fpprod, list.partial_prod] at * },
      { use hl,
        simp } },
    { rw [mem_partial_prod_reverse_inv hw1, list.mem_map] at hw',
      rcases hw' with ⟨w, hw', rfl⟩ | rfl,
      { refine ⟨w, hw', _⟩,
        simp [exp_sum_eq_one_of_mem_closure_var h₁ (not_not.2 rfl)] },
      { exfalso,
        dsimp at hv1,
        erw [fprod, map_prod_of_eq_self] at hv1,
        simp [exp_sum_eq_one_of_mem_closure_var h₁ (not_not.2 rfl)] at hv1,
        tauto } } },
  { rw mem_map at hv,
    rcases hv with ⟨w, hw, rfl⟩,
    rw [monoid_hom.map_mul, exp_sum_eq_one_of_mem_closure_var
      (partial_prod_mem_blah hw h₁) (not_not.2 rfl), one_mul] at hv1 ⊢,
    use fprod l,
    rcases prod_mem_partial_prod (l.map (λ i : Σ i : ι, C∞, of' i.1 i.2)) with hl | hl,
    { simp [*, fpprod, list.partial_prod, fprod] at * },
    { use hl } },
  { use [v, hv, rfl] }
end

@[simp] lemma list.map_id'' {α : Type*} (l : list α) :
  l.map (λ x, x) = l := list.map_id l

lemma append_inv_reverse_exp_sum_eq_one {n : C∞} {t : ι} {l : list (Σ i : ι, C∞)} {r : free_group ι}
  (h₁ : r ∈ closure_var {i | i ≠ t})
  (h₂ : ∀ v, v ∈ fpprod l → n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1) :
  ∀ v ∈ fpprod ((l.map (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse ++ r.to_list ++ l),
    n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1 :=
begin
  assume v hv hn,
  by_contra hv1,
  rcases exp_sum_append_subset h₁ v hv hv1 with ⟨w, hw, hwv⟩,
  exact hv1 (hwv.symm ▸ h₂ w hw (hwv ▸ hn))
end

lemma append_conj_append_exp_sum_eq_one {n : C∞} {t : ι} {l₁ l₂ : list (Σ i : ι, C∞)} {r : free_group ι}
  (h₁ : r ∈ closure_var {i | i ≠ t})
  (h₂ : ∀ v, v ∈ fpprod l₁ → n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1)
  (h₃ : exp_sum t (fprod l₂) = 1)
  (h₄ : ∀ v, v ∈ fpprod l₂ → n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1) :
  ∀ v ∈ fpprod ((l₁.map (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
      ++ r.to_list ++ l₁ ++ l₂),
    n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1 :=
begin
  assume v hv hn,
  rw [fpprod, map_append, partial_prod_append, mem_append] at hv,
  cases hv with hv hv,
  { rw [mem_map] at hv,
    rcases hv with ⟨w, hw, rfl⟩,
    erw [monoid_hom.map_mul, h₃, mul_one] at hn ⊢,
    exact append_inv_reverse_exp_sum_eq_one h₁ h₂ _ hw hn },
  { exact h₄ _ hv hn }
end

lemma exp_sum_bind_conj {t : ι} {r : free_group ι} (L : list (list (Σ i : ι, C∞) × C∞))
  (h₁ : r ∈ closure_var {i | i ≠ t}) :
  exp_sum t (fprod (L.bind (λ l, (l.1.map (λ i : Σ i : ι, C∞,
    (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
      ++ (r ^ to_add l.2).to_list ++ l.1))) = 1 :=
begin
  induction L with l L ih,
  { simp [fprod] },
  { rw [cons_bind, fprod, map_append, prod_append, ← fprod, ← fprod,
      monoid_hom.map_mul, ih, mul_one],
    simp [fprod, function.comp],
    erw [map_prod_of_eq_self (r ^ to_add l.2),
      exp_sum_eq_one_of_mem_closure_var (subgroup.gpow_mem _ h₁ _) (not_not.2 rfl),
      one_mul],
    induction l.1 with i l ih,
    { simp },
    { simp; split_ifs; simp [mul_assoc, ih] } }
end

lemma bind_conj_exp_sum_eq_one {t : ι} (n : C∞) {r : free_group ι}
  (L : list (list (Σ i : ι, C∞) × C∞))
  (h₁ : r ∈ closure_var {i | i ≠ t})
  (h₂ : ∀ l : list (Σ i : ι, C∞) × C∞, l ∈ L →
    ∀ v, v ∈ fpprod l.1 → n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1) :
    ∀ v ∈ fpprod (L.bind (λ l,
      (l.1.map (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
      ++ (r ^ to_add l.2).to_list ++ l.1)),
     n.to_add ∣ (exp_sum t v).to_add → exp_sum t v = 1 :=
begin
  assume v hv hn,
  induction L with l L ih generalizing v,
  { simp [fpprod, *, list.partial_prod] at * },
  { rw [cons_bind] at hv,
    rcases prod_mem_partial_prod ((L.bind (λ l, (l.1.map
      (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
      ++ (r ^ to_add l.2).to_list ++ l.1)).map (λ i : Σ i : ι, C∞, of' i.1 i.2)) with hL | hL,
    { rw [fpprod, map_append, hL, append_nil] at hv,
      exact append_inv_reverse_exp_sum_eq_one (subgroup.gpow_mem _ h₁ _)
        (h₂ _ (mem_cons_self _ _)) _ hv hn },
    { exact append_conj_append_exp_sum_eq_one (subgroup.gpow_mem _ h₁ _)
        (h₂ l (mem_cons_self _ _)) (exp_sum_bind_conj _ h₁)
        (ih (λ l hl, h₂ l (mem_cons_of_mem _ hl))) _ hv hn } }
end

lemma map_reverse_eq_inv {l : list (Σ i : ι, C∞)} :
  (map (λ (i : Σ i : ι, C∞), (of' i.fst) i.snd)
    (map (λ (i : Σ i : ι, C∞), (⟨i.fst, (i.snd)⁻¹⟩ : Σ i : ι, C∞)) l).reverse).prod =
  (fprod l)⁻¹:=
begin
  induction l with i l ih,
  { simp [fprod] },
  { rw [map_cons, reverse_cons, map_append, prod_append, ih],
    simp [mul_assoc, fprod] }
end

-- lemma bind_conj_eq_lift {r : free_group ι} (p : free_group (free_group ι)) :
--   fprod ((p.to_list.map (λ l : Σ i : free_group ι, C∞, (l.1.to_list, l.2))).bind
--     (λ l, (l.1.map (λ i : Σ i : ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
--       ++ (r ^ to_add l.2).to_list ++ l.1)) = lift (λ g, g⁻¹ * r * g) p :=
-- begin
--   cases p with L hL,
--   induction L with l L ih,
--   { simp [fprod] },
--   { erw [map_cons, cons_bind, fprod, map_append, prod_append, ← fprod,
--       ← fprod, ih (coprod.pre.reduced_of_reduced_cons hL),
--       cons_eq_of'_mul, monoid_hom.map_mul, mul_right_cancel_iff,
--       free_group.lift, lift'_of', fprod, map_append, map_append,
--       prod_append, prod_append, map_prod_of_eq_self, map_prod_of_eq_self,
--       map_reverse_eq_inv l.1.2, ← mul_aut.conj_symm_apply _ (r ^ _),
--       ← mul_equiv.to_monoid_hom_apply, monoid_hom.map_gpow],
--     simp [gpowers_hom] }
-- end

lemma dvd_exp_sum_of_mem_blah {t : ι} {n : C∞} {w : free_group ι}
  (h : w ∈ blah (λ i : ι, ⨅ (h : t = i), subgroup.gpowers n)) :
  n.to_add ∣ (exp_sum t w).to_add :=
begin
  rw [← range_pow_single] at h,
  rcases h with ⟨v, rfl⟩,
  rw [← monoid_hom.comp_apply, exp_sum_comp_pow_single],
  simp [gpowers_hom]
end

def of_option (t : ι) (n : C∞) : free_group (option ι) →* free_group ι :=
free_group.lift (λ i : option ι, i.elim (of' t n) of)

lemma of_option_of' (t : ι) (i : option ι) (n m : C∞) : of_option t n (of' i m) =
  i.elim (of' t n ^ to_add m) (λ i, of' i m) :=
by simp [of_option, of'_eq_of_pow, monoid_hom.map_gpow]; cases i;
  simp [monoid_hom.map_gpow, gpow_add]

--true
-- lemma mem_thing {t : ι} {n : C∞}
--   {r : free_group (option ι)}
--   {p : free_group (free_group ι)}
--   (h : of_option t n (fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
--     ((eliminate_t t n w.1.to_list).1, w.2))).bind
--       (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
--         ++ (r ^ to_add l.2).to_list ++ l.1))) ∈ (pow_single t n).range) :
--   fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
--     ((eliminate_t t n w.1.to_list).1, w.2))).bind
--       (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
--         ++ (r ^ to_add l.2).to_list ++ l.1)) ∈ (pow_single (some t) n).range :=
-- begin
--   cases p with L hL,
--   induction L with w L ih,
--   { simp [fprod, subgroup.one_mem] },
--   { erw [cons_bind, fprod, map_append, prod_append, ← fprod, ← fprod],
--     refine subgroup.mul_mem _ _ _, }

-- end

-- lemma of_option_eliminate_t_conj_prod_mem_closure_var {t : ι} {n : C∞}
--   {r : free_group (option ι)}
--   {p : free_group (free_group ι)}
--   (hr : r ∈ closure_var {i | i ≠ some t})
--   (hp : of_option t n (fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
--     ((eliminate_t t n w.1.to_list).1, w.2))).bind
--       (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
--         ++ (r ^ to_add l.2).to_list ++ l.1))) ∈ (pow_single t n).range) :
--   of_fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
--     ((eliminate_t t n w.1.to_list).1, w.2))).bind
--       (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
--         ++ (r ^ to_add l.2).to_list ++ l.1)) ∈ closure_var {i | some t ≠ i} :=
-- begin
--   apply mem_closure_var_of_forall_exp_sum_eq_one,
--   assume v hv,
--   have hv' := (partial_prod_sublist _).subset hv,
--   refine bind_conj_exp_sum_eq_one n _ hr _ _ hv' _,
--   { assume l hl v hv hn,
--     rw [mem_map] at hl,
--     rcases hl with ⟨w, hw, rfl⟩,
--     exact eliminate_t_exp_sum_eq_one _ _ _ _ hv hn },
--   { refine dvd_exp_sum_of_mem_blah (partial_prod_mem_blah hv _),
--     rw [← range_pow_single],
--     exact hp }
-- end

lemma prod_bind_conj_eq_lift {t : ι} {n : C∞} (r : free_group (option ι))
  (p : free_group (free_group ι))  :
    (fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
      ((eliminate_t t n w.1.to_list).1, w.2))).bind
        (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
          ++ (r ^ to_add l.2).to_list ++ l.1))) =
  free_group.lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
    mul_aut.conj w⁻¹ r) p :=
begin
  cases p with L hL,
  induction L with w L ih,
  { simp [fprod] },
  { erw [fprod, map_cons, cons_bind, map_append, prod_append, ← fprod, ← fprod,
      ih (coprod.pre.reduced_of_reduced_cons hL)],
    conv_rhs { rw [cons_eq_of'_mul, monoid_hom.map_mul] },
    erw [mul_right_cancel_iff, of'_eq_of_pow, monoid_hom.map_gpow, lift_of,
      fprod, map_append, map_append, prod_append, prod_append,
      map_prod_of_eq_self (r ^ _), map_reverse_eq_inv],
    dsimp only,
    rw [← mul_equiv.to_monoid_hom_apply, ← monoid_hom.map_gpow],
    simp [mul_aut.inv_def, mul_aut.conj_symm_apply] }
end

--IMPORTANT
lemma eliminate_t_conj_prod_mem_closure_var {t : ι} {n : C∞}
  {r : free_group (option ι)}
  {p : free_group (free_group ι)}
  (hr : r ∈ closure_var {i | i ≠ some t})
  (hp : fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
    ((eliminate_t t n w.1.to_list).1, w.2))).bind
      (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
        ++ (r ^ to_add l.2).to_list ++ l.1)) ∈ (pow_single (some t) n).range) :
  fprod ((p.to_list.map (λ w : Σ i : free_group ι, C∞,
    ((eliminate_t t n w.1.to_list).1, w.2))).bind
      (λ l, (l.1.map (λ i : Σ i : option ι, C∞, (⟨i.1, i.2⁻¹⟩ : Σ i, C∞))).reverse
        ++ (r ^ to_add l.2).to_list ++ l.1)) ∈ closure_var {i | some t ≠ i} :=
begin
  apply mem_closure_var_of_forall_exp_sum_eq_one,
  assume v hv,
  have hv' := (partial_prod_sublist _).subset hv,
  refine bind_conj_exp_sum_eq_one n _ hr _ _ hv' _,
  { assume l hl v hv hn,
    rw [mem_map] at hl,
    rcases hl with ⟨w, hw, rfl⟩,
    exact eliminate_t_exp_sum_eq_one _ _ _ _ hv hn },
  { refine dvd_exp_sum_of_mem_blah (partial_prod_mem_blah hv _),
    rw [prod_bind_conj_eq_lift] at ⊢ hp,
    rw [← range_pow_single],
    exact hp }
end

lemma pow_single_map {t : ι} {n : C∞} (w : free_group ι):
  (pow_single (some t) n) (map some w) = map some ((pow_single t n) w) :=
begin
  simp only [← monoid_hom.comp_apply],
  refine congr_fun (congr_arg _ (hom_ext $ λ i, _)) _,
  simp [pow_single],
  split_ifs;
  simp [of'_eq_of_pow, monoid_hom.map_gpow]
end

lemma map_mem_range {t : ι} {n : C∞} {r : free_group ι}
  (hr : r ∈ (pow_single t n).range) :
  free_group.map some r ∈ (pow_single (some t) n).range :=
begin
  rcases monoid_hom.mem_range.1 hr with ⟨w, rfl⟩,
  rw [← pow_single_map],
  exact ⟨_, rfl⟩
end

lemma eliminate_t_conj_lift_mem_closure_var {t : ι} {n : C∞}
  {r : free_group (option ι)}
  {p : free_group (free_group ι)}
  (hr : r ∈ closure_var {i | i ≠ some t}) :
  lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
    mul_aut.conj w⁻¹ r) p ∈ (pow_single (some t) n).range →
 lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
    mul_aut.conj w⁻¹ r) p ∈ closure_var {i | some t ≠ i} :=
begin
  convert eliminate_t_conj_prod_mem_closure_var hr,
  rw prod_bind_conj_eq_lift
end

lemma lift_eliminate_t_conj_eq_lift (t : ι) {n : C∞} (hn : n ≠ 1)
  {r : free_group (option ι)} :
  free_group.lift (λ w, mul_aut.conj w⁻¹ (of_option t n r)) =
  (of_option t n).comp
    (lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
      mul_aut.conj w⁻¹ r)) :=
hom_ext begin
  assume w,
  simp only [mul_aut.inv_def, mul_aut.conj_symm_apply, monoid_hom.map_mul,
    monoid_hom.map_inv, monoid_hom.comp_apply, lift_of, of_option],
  erw [prod_eliminate_t _ _ _ hn, fprod, map_prod_of_eq_self]
end

lemma lift_eliminate_t_mem_range {t : ι} {n : C∞} (hn : n ≠ 1)
  {r : free_group (option ι)} (hr : of_option t n r ∈ (pow_single t n).range)
  {p : free_group (free_group ι)}
  (h : free_group.lift (λ w, mul_aut.conj w⁻¹ (of_option t n r)) p ∈ (pow_single t n).range) :
  lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
    mul_aut.conj w⁻¹ r) p ∈ (pow_single (some t) n).range := sorry

lemma lift_ite_eq_self_of_mem_closure_var {t : ι} {w : free_group ι}
  (hw : w ∈ closure_var {i | t ≠ i}) : free_group.lift (λ i, if i = t then 1 else of i) w = w :=
begin
  cases w with l hl,
  induction l with i l ih,
  { simp },
  { rw [cons_eq_of'_mul, monoid_hom.map_mul, ih
      (coprod.pre.reduced_of_reduced_cons hl) (λ i hi, hw i (mem_cons_of_mem _ hi)),
      of'_eq_of_pow, monoid_hom.map_gpow, lift_of],
    split_ifs,
    { have := hw i (mem_cons_self _ _),
      simp [h] at this,
      simp [this] },
    { refl } }
end

lemma lift_eliminate_t_eq_self_of_mem_pow_range {t : ι} {n : C∞} (hn : n ≠ 1)
  {r : free_group (option ι)} {p : free_group (free_group ι)}
  (hp : free_group.lift (λ w, mul_aut.conj w⁻¹ (of_option t n r)) p ∈ (pow_single t n).range)
  (hr : r ∈ closure_var {i : option ι | i ≠ some t}) :
  free_group.lift (λ i : option ι, i.elim (of' t n) (λ i, if i = t then 1 else of i))
    (free_group.lift (λ w, mul_aut.conj w⁻¹ r)
      (free_group.map (λ w : free_group ι, (fprod (eliminate_t t n w.to_list).1)) p)) =
  free_group.lift (λ w, mul_aut.conj w⁻¹ (of_option t n r)) p :=
calc free_group.lift (λ i : option ι, i.elim (of' t n) (λ i, if i = t then 1 else of i))
    (free_group.lift (λ w, mul_aut.conj w⁻¹ r)
      (free_group.map (λ w : free_group ι, (fprod (eliminate_t t n w.to_list).1)) p)) =
    of_option t n
     (free_group.lift (λ i : option ι, if i = some t then 1 else of i)
    ((free_group.lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
      mul_aut.conj w⁻¹ r)) p)) :
  begin
    simp only [← monoid_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    refine hom_ext _,
    assume i,
    simp only [← monoid_hom.comp_apply],
    have : free_group.lift (λ i : option ι, i.elim (of' t n)
        (λ (i : ι), ite (i = t) 1 (of i))) =
        (of_option t n).comp
          (free_group.lift (λ i : option ι, ite (i = some t) 1 (of i))),
      from hom_ext (λ i, option.cases_on i (by simp [of_option, of'_eq_of_pow])
        (λ i, by simp; split_ifs; simp [*, of_option])),
    refine congr_fun (congr_arg _ _) _,
    refine hom_ext _,
    assume i,
    simp [this, monoid_hom.comp_apply, of_option],
  end
... = of_option t n
    ((free_group.lift (λ w : free_group ι, let w := fprod (eliminate_t t n w.to_list).1 in
      mul_aut.conj w⁻¹ r)) p) :
  begin
    unfold of_option,
    refine congr_arg _ _,
    refine lift_ite_eq_self_of_mem_closure_var _,
    refine eliminate_t_conj_lift_mem_closure_var hr _,
    refine lift_eliminate_t_mem_range hn sorry hp,
  end
... = _ : by rw [← monoid_hom.comp_apply, lift_eliminate_t_conj_eq_lift _ hn]
-- lemma prod_mem_of_eliminate_t_mem (t : ι) (n : C∞)
--   (l : list (Σ i : ι, C∞)) (hn : n ≠ 1)
--   (h : ((eliminate_t t n l).1.map (λ i : Σ i : option ι, C∞, of' i.1 i.2)).prod ∈
--     (pow_single (some t) n).range) :
--   ((eliminate_t t n l).1.map (λ i : Σ i : option ι, C∞, of' i.1 i.2)).prod ∈
--     closure_var {i | some t ≠ i} :=
-- mem_closure_var_of_forall_exp_sum_eq_one $ λ w hw,
--   eliminate_t_exp_sum_eq_one _ _ _ _
--     ((partial_prod_sublist _).subset hw)
--     (dvd_exp_sum_of_mem_blah
--       ((mem_blah_iff_partial_prod_mem_blah _ _).2 (by rwa [← range_pow_single]) w hw))

-- def pow_proof_aux (t : ι) (n s : C∞) : Π (l : list (Σ i : ι, C∞)), free_group ι × C∞
-- | []     := (1, s)
-- | (i::l) := let w := pow_proof_aux l in
-- if t = i.1
--   then if n.to_add ∣ to_add i.2 + to_add w.2
--     then (of' t (of_add ((to_add i.2 + to_add w.2) / n.to_add)) * w.1, 1)
--     else (w.1, i.2 * w.2)
--   else (of' i.1 i.2 * w.1, w.2)

-- lemma pow_proof_append (t : ι) (n : C∞) (s : C∞) : Π (l₁ l₂ : list (Σ i : ι, C∞)),
--   pow_proof t n s (l₁ ++ l₂) = ((pow_proof t n (pow_proof t n s l₂).2 l₁).1 * (pow_proof t n s l₂).1,
--     (pow_proof t n (pow_proof t n s l₂).2 l₁).2)
-- | []      l₂ := by simp [pow_proof]
-- | (i::l₁) l₂ := begin
--   rw [cons_append, pow_proof, pow_proof_append],
--   simp [pow_proof],
--   split_ifs; simp [mul_assoc]
-- end

/-- tail recursive pow_proof -/
def pow_proof_core (t : ι) (n : C∞) : Π (l : list (Σ i : ι, C∞)), free_group ι × C∞ → free_group ι × C∞
| []     w := w
| (i::l) w :=
if t = i.1
  then if n.to_add ∣ to_add i.2 + to_add w.2
    then pow_proof_core l (w.1 * of' t (of_add ((to_add i.2 + to_add w.2) / n.to_add)), 1)
    else pow_proof_core l (w.1, i.2 * w.2)
  else pow_proof_core l (w.1 * of' i.1 i.2, w.2)


def pow_proof (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) : free_group ι :=
(pow_proof_core t n l 1).1

#eval (pow_proof 0 (of_add 2) [⟨2, of_add 1⟩, ⟨1, of_add 1⟩, ⟨3, of_add 1⟩]).1

#eval (pow_proof 0 (of_add 2) [⟨1, of_add 2⟩, ⟨3, of_add 2⟩]).1

lemma pow_proof_core_append (t : ι) (n : C∞) : Π (l₁ l₂ : list (Σ i : ι, C∞)) (w : free_group ι × C∞) ,
  pow_proof_core t n (l₁ ++ l₂) w = pow_proof_core t n l₂ (pow_proof_core t n l₁ w)
| []      l₂ w := rfl
| (i::l₁) l₂ w :=
begin
  rw [cons_append, pow_proof_core, pow_proof_core_append, pow_proof_core],
  split_ifs; simp [pow_proof_core_append, pow_proof_core],
end

def eliminate_t' (t : ι) (n s : C∞) : list (Σ i : ι, C∞) → list (Σ i : option ι, C∞) × C∞
| []     := ([], s)
| (i::l) :=
let x := eliminate_t' l in
if t = i.1
  then if n.to_add ∣ to_add i.2 + to_add x.2
    then (⟨none, of_add ((to_add i.2 + to_add x.2) / n.to_add)⟩ ::
      ⟨some i.1, x.2⁻¹⟩ :: x.1, 1)
    else (⟨some i.1, i.2⟩ :: x.1, i.2 * x.2)
  else (⟨some i.1, i.2⟩ :: x.1, x.2)

@[simp] lemma eliminate_t'_one (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
  eliminate_t' t n 1 l = eliminate_t t n l :=
by induction l; simp [*, eliminate_t, eliminate_t']

lemma pow_proof_core_snd (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) (w : free_group ι × C∞) :
  (pow_proof_core t n l.reverse w).2 = (eliminate_t' t n w.2 l).2 :=
begin
  induction l with i l ih,
  { simp [pow_proof_core, eliminate_t'] },
  { simp [pow_proof_core, eliminate_t', pow_proof_core_append, ih],
    split_ifs; refl }
end

lemma pow_proof_core_eq_eliminate_t' (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) (w : free_group ι × C∞) :
  (pow_proof_core t n l.reverse w).1 = w.1 * free_group.lift
    (λ i : option ι, i.elim (of t) (λ i, if i = t then 1 else of i))
    (fprod (eliminate_t' t n w.2 l).1.reverse):=
begin
  induction l with i l ih generalizing w,
  { simp [pow_proof_core, eliminate_t', fprod] },
  { simp [pow_proof_core_append, pow_proof_core, eliminate_t', pow_proof_core_snd],
    split_ifs,
    { simp [ih, fprod, mul_assoc, ← h, gpowers_hom, of'_eq_of_pow, monoid_hom.map_gpow] },
    { simp [ih, fprod, mul_assoc, ← h, gpowers_hom, of'_eq_of_pow, monoid_hom.map_gpow] },
    { simp [ih, fprod, mul_assoc, gpowers_hom, of'_eq_of_pow, monoid_hom.map_gpow, ne.symm h] } }
end

lemma pow_proof_eq_eliminate_t (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
  pow_proof t n l.reverse = free_group.lift
    (λ i : option ι, i.elim (of t) (λ i, if i = t then 1 else of i))
    (fprod (eliminate_t t n l).1.reverse) :=
by simp [pow_proof, pow_proof_core_eq_eliminate_t']

def pow_single_inverse_aux (t : ι) (n : C∞) : list (Σ i : ι, C∞) → option (list Σ i : ι, C∞)
| []    := some []
| (i::l)  :=
do l' ← pow_single_inverse_aux l,
if i.1 = t
  then if to_add n ∣ i.2
    then return (⟨i.1, of_add $ to_add i.2 / to_add n⟩ :: l')
    else none
  else i :: l'

lemma pow_single_inverse_aux_reduced (t : ι) (n : C∞) :
  ∀ l : list (Σ i : ι, C∞), coprod.pre.reduced l →
    ∀ l' ∈ pow_single_inverse_aux t n l, coprod.pre.reduced l' := sorry

def pow_single_inverse (t : ι) (n : C∞) (w : free_group ι) : option (free_group ι) :=
begin
  cases h : pow_single_inverse_aux t n w.1,
  { exact none },
  { exact some ⟨val, pow_single_inverse_aux_reduced t n w.1 w.2 _ h⟩ }
end

def pow_single_pullback (t : ι) (n : C∞) (p : P (free_group ι)) : option (P (free_group ι)) :=
(pow_single_inverse t n p.2).map (λ w, ⟨map (λ w : free_group ι, pow_proof t n w.to_list) p.1, w⟩)

#eval (pow_single_pullback 0 (of_add 3) ⟨of (of 0 ^(-6 : ℤ) * of 2 * of 1) * of (of 1)⁻¹, 1⟩).iget.left


-- lemma pow_proof_core_eq' (t : ι) (n : C∞) : ∀ (l₁ l₂ : list (Σ i : ι, C∞)) (s : C∞),
--   pow_proof_core t n l₂.reverse (pow_proof_aux t n s l₁) =
--     pow_proof_aux t n s (l₁ ++ l₂)
-- | []        [] s := rfl
-- | []  (i ::l₂) s := begin
--   simp [pow_proof_aux,],


-- end
-- | []        l₂ s := by simp [pow_proof_core, pow_proof_aux]
-- | (i::l₁)   l₂ s := begin
--   simp only [reverse_cons, pow_proof_core_append, pow_proof_core, pow_proof_core,
--     cons_append, pow_proof_aux],
--   simp only [pow_proof_core_eq'],
--   split_ifs, simp [mul_assoc, pow_proof_aux],
-- end


-- lemma pow_proof_core_eq (t : ι) (n : C∞) : ∀ (l : list (Σ i : ι, C∞)) (w : free_group ι × C∞),
--   pow_proof_core t n l.reverse w = (w.1 * (pow_proof_aux t n w.2 l).1 * w.1, (pow_proof_aux t n w.2 l).2)
-- | []     w := by simp [pow_proof_core, pow_proof_aux]
-- | (i::l) w := begin
--   simp only [reverse_cons, pow_proof_core_append, pow_proof_core, pow_proof_core, pow_proof_aux],
--   simp only [pow_proof_core_eq],
--   split_ifs; simp [mul_assoc]
-- end

-- lemma pow_proof_eq (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
--   pow_proof t n l = (pow_proof_aux t n 1 l.reverse).1 :=
-- begin
--   rw [← reverse_reverse l, pow_proof, pow_proof_core_eq],
--   simp,
-- end

-- lemma pow_proof_aux_snd (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
--   (pow_proof_aux t n 1 l).2 = (eliminate_t t n l).2 :=
-- begin
--   induction l with i l ih,
--   { refl },
--   { simp [pow_proof_aux, eliminate_t],
--     split_ifs; simp * at * }
-- end

-- lemma pow_proof_aux_eq_eliminate_t (t : ι) (n : C∞) : ∀ (l : list (Σ i : ι, C∞)),
--   (pow_proof_aux t n 1 l).1 = free_group.lift
--     (λ i : option ι, i.elim (of t) (λ i, if i = t then 1 else of i))
--     (fprod (eliminate_t t n l).1)
-- | []     := by simp [pow_proof_aux, eliminate_t, fprod]
-- | (i::l) := begin
--   simp only [pow_proof_aux, fprod, eliminate_t, pow_proof_aux_eq_eliminate_t l, pow_proof_aux_snd],
--   split_ifs;
--   simp [*, monoid_hom.map_list_prod, of_eq_of', free_group.lift, gpowers_hom, @eq_comm _ _ t];
--   simp [of'_eq_of_pow]
-- end

-- lemma pow_proof_eq_eliminate_t (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
--   pow_proof t n l = free_group.lift
--     (λ i : option ι, i.elim (of t) (λ i, if i = t then 1 else of i))
--     (fprod (eliminate_t t n l.reverse).1) :=
-- by rw [pow_proof_eq, pow_proof_aux_eq_eliminate_t]


-- -- lemma pow_proof_snd_append_of_pow_proof_snd_eq_one
-- --   {t : ι} {n : C∞} {l₁ l₂ : list (Σ i : ι, C∞)}
-- --   (hl : (pow_proof t n l₂).2 = 1) :
-- --   (pow_proof t n (l₁ ++ l₂)).2 = (pow_proof t n l₁).2  :=
-- -- begin
-- --   induction l₁ with i l₁ ih,
-- --   { simp [pow_proof, hl] },
-- --   { simp [list.cons_append, pow_proof, ih],
-- --     split_ifs; refl }
-- -- end

-- -- lemma pow_proof_append_of_pow_proof_snd_eq_one {t : ι} {n : C∞} {l₁ l₂ : list (Σ i : ι, C∞)}
-- --   (hl : (pow_proof t n l₂).2 = 1) :
-- --   (pow_proof t n (l₁ ++ l₂)).1 = (pow_proof t n l₁).1 * (pow_proof t n l₂).1 :=
-- -- begin
-- --   induction l₁ with i l₁ ih,
-- --   { simp [pow_proof], },
-- --   { rw [list.cons_append, pow_proof],
-- --     dsimp,
-- --     rw ih,
-- --     simp [pow_proof, pow_proof_snd_append_of_pow_proof_snd_eq_one hl],
-- --     split_ifs,
-- --     { simp [mul_assoc, ih, hl] },
-- --     { refl },
-- --     { rw [mul_assoc] } }
-- -- end
