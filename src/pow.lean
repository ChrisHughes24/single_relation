import for_mathlib.coprod.free_group_subgroup
import .functor

variables {ι : Type} {M : ι → Type}
variables [decidable_eq ι] [Π i, decidable_eq (M i)]
variables [Π i, monoid (M i)]

section partial_prod

open coprod

/-- `partial_prod l` returns the list of products of final segments of `l`.
  e.g. `partial_prod [a, b, c]` = `[a * b * c, b * c, c]`  -/
def list.partial_prod {M : Type*} [monoid M] : list M → list M
| []     := []
| (a::l) := (a::l : list _).prod :: list.partial_prod l

lemma prod_mem_partial_prod {M : Type*} [monoid M] (l : list M) :
  l.prod = 1 ∨ l.prod ∈ l.partial_prod :=
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
  { assume i, admit },
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

@[simp] lemma to_add_pow (a : multiplicative ℤ) (b : ℕ) : to_add (a ^ b) = to_add a * b :=
by induction b; simp [*, mul_add, pow_succ, add_comm]

@[simp] lemma to_add_gpow (a : multiplicative ℤ) (b : ℤ) : to_add (a ^ b) = to_add a * b :=
int.induction_on b (by simp)
  (by simp [gpow_add, mul_add] {contextual := tt})
  (by simp [gpow_add, mul_add, sub_eq_add_neg] {contextual := tt})

@[simp] lemma of_add_mul (a b : ℤ) : of_add (a * b) = of_add a ^ b :=
(to_add_gpow _ _).symm

lemma dvd_exp_sum_of_mem_blah {t : ι} {n : C∞} {w : free_group ι}
  (h : w ∈ blah (λ i : ι, ⨅ (h : t = i), subgroup.gpowers n)) :
  n.to_add ∣ (exp_sum t w).to_add :=
begin
  rw [← range_pow_single] at h,
  rcases h with ⟨v, rfl⟩,
  rw [← monoid_hom.comp_apply, exp_sum_comp_pow_single],
  simp [gpowers_hom]
end

lemma prod_mem_of_eliminate_t_mem (t : ι) (n : C∞)
  (l : list (Σ i : ι, C∞)) (hn : n ≠ 1)
  (h : ((eliminate_t t n l).1.map (λ i : Σ i : option ι, C∞, of' i.1 i.2)).prod ∈
    (pow_single (some t) n).range) :
  ((eliminate_t t n l).1.map (λ i : Σ i : option ι, C∞, of' i.1 i.2)).prod ∈
    closure_var {i | some t ≠ i} :=
mem_closure_var_of_forall_exp_sum_eq_one $ λ w hw,
  eliminate_t_exp_sum_eq_one _ _ _ _
    ((partial_prod_sublist _).subset hw)
    (dvd_exp_sum_of_mem_blah
      ((mem_blah_iff_partial_prod_mem_blah _ _).2 (by rwa [← range_pow_single]) w hw))

def pow_proof (t : ι) (n : C∞) : Π (l : list (Σ i : ι, C∞)), free_group ι × C∞
| []     := 1
| (i::l) := let w := pow_proof l in
if t = i.1
  then if n.to_add ∣ to_add i.2 + to_add w.2
    then (of' t (of_add ((to_add i.2 + to_add w.2) / n.to_add)) * w.1, 1)
    else (w.1, i.2 * w.2)
  else (of' i.1 i.2 * w.1, w.2)

lemma pow_proof_snd (t : ι) (n : C∞) (l : list (Σ i : ι, C∞)) :
  (pow_proof t n l).2 = (eliminate_t t n l).2 :=
begin
  induction l with i l ih,
  { refl },
  { simp [pow_proof, eliminate_t],
    split_ifs; simp * at * }
end

lemma pow_proof_eq_eliminate_t (t : ι) (n : C∞) : ∀ (l : list (Σ i : ι, C∞)),
  (pow_proof t n l).1 = free_group.lift
    (λ i : option ι, i.elim (of t) (λ i, if i = t then 1 else of i))
    (fprod (eliminate_t t n l).1)
| []     := by simp [pow_proof, eliminate_t, fprod]
| (i::l) := begin
  simp only [pow_proof, fprod, eliminate_t, pow_proof_eq_eliminate_t l, pow_proof_snd],
  split_ifs;
  simp [*, monoid_hom.map_list_prod, of_eq_of', free_group.lift,
    gpowers_hom, @eq_comm _ _ t];
  simp [of'_eq_of_pow]
end

-- lemma pow_proof_snd_append_of_pow_proof_snd_eq_one
--   {t : ι} {n : C∞} {l₁ l₂ : list (Σ i : ι, C∞)}
--   (hl : (pow_proof t n l₂).2 = 1) :
--   (pow_proof t n (l₁ ++ l₂)).2 = (pow_proof t n l₁).2  :=
-- begin
--   induction l₁ with i l₁ ih,
--   { simp [pow_proof, hl] },
--   { simp [list.cons_append, pow_proof, ih],
--     split_ifs; refl }
-- end

-- lemma pow_proof_append_of_pow_proof_snd_eq_one {t : ι} {n : C∞} {l₁ l₂ : list (Σ i : ι, C∞)}
--   (hl : (pow_proof t n l₂).2 = 1) :
--   (pow_proof t n (l₁ ++ l₂)).1 = (pow_proof t n l₁).1 * (pow_proof t n l₂).1 :=
-- begin
--   induction l₁ with i l₁ ih,
--   { simp [pow_proof], },
--   { rw [list.cons_append, pow_proof],
--     dsimp,
--     rw ih,
--     simp [pow_proof, pow_proof_snd_append_of_pow_proof_snd_eq_one hl],
--     split_ifs,
--     { simp [mul_assoc, ih, hl] },
--     { refl },
--     { rw [mul_assoc] } }
-- end
