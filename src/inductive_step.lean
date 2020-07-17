import .coproduct group_theory.semidirect_product data.set.lattice

noncomputable theory

universe u

open semidirect_product

lemma inl_aut_inv {G : Type*} {N : Type*} [group G] [group N]
  (φ : G →* mul_aut N) (g : G) (n : N) :
  (semidirect_product.inl ((φ g)⁻¹ n) : N ⋊[φ] G) =
  semidirect_product.inr g⁻¹ * semidirect_product.inl n * semidirect_product.inr g :=
sorry

@[simp] lemma mk_eq_inl_mul_inr {G : Type*} {N : Type*} [group G] [group N]
  (φ : G →* mul_aut N) (g : G) (n : N) : (⟨n, g⟩ : N ⋊[φ] G) =
  semidirect_product.inl n * semidirect_product.inr g :=
by ext; simp

lemma semidirect_product.hom_ext {G : Type*} {N : Type*} [group G]
  [group N] {H : Type*} [group H]
  {φ : G →* mul_aut N} {f g : (N ⋊[φ] G) →* H} (hl : f.comp inl = g.comp inl)
  (hr : f.comp inr = g.comp inr) : f = g :=
by { rw [lift_unique f, lift_unique g], simp only * }

variables {ι : Type} [decidable_eq ι] (r : free_group ι) (T : set ι) [decidable_pred T]

open free_group

def phi : closure_var T →* mul_aut (free_group (free_group ι)) :=
{ to_fun := λ g : closure_var T, free_group.equiv (mul_left (g : free_group ι)),
  map_one' := by simp [equiv.perm.one_def]; refl,
  map_mul' := λ x y, by simp [equiv.perm.mul_def]; refl }

def phi' : free_group ι →* mul_aut (free_group (free_group ι)) :=
{ to_fun := λ w, free_group.equiv (mul_left w),
  map_one' := by simp [equiv.perm.one_def, mul_aut.one_def],
  map_mul' := by simp [equiv.perm.mul_def, mul_aut.mul_def] }

lemma phi'_of' (n : C∞) (w w' : free_group ι) :
  phi' w (of' w' n) = of' (w * w') n := by simp [phi']

include r

def unnormalize : free_group (free_group ι) ⋊[phi T] closure_var T →* free_group ι :=
semidirect_product.lift
  (free_group.lift' (λ g : free_group ι,
    (mul_aut.conj g : free_group ι ≃* free_group ι).to_monoid_hom.comp
      (gpowers_hom (free_group ι) r)))
  (subgroup.subtype (closure_var T))
  (λ g, hom_ext (λ i, by simp [_root_.phi, of_eq_of']))

open semidirect_product

def unnormalize' : free_group (free_group ι) ⋊[phi'] free_group ι →* free_group ι :=
semidirect_product.lift
  (free_group.lift' (λ g : free_group ι,
    (mul_aut.conj g : free_group ι ≃* free_group ι).to_monoid_hom.comp
      (gpowers_hom (free_group ι) r)))
  (monoid_hom.id _)
  (λ g, hom_ext (λ i, by simp [_root_.phi', of_eq_of']))

@[simp] lemma unnormalize'_inr (w : free_group ι) : unnormalize' r (inr w) = w :=
semidirect_product.lift_inr _ _ _ _

lemma unnormalize'_inl (w : free_group (free_group ι)) :
  unnormalize' r (inl w) = free_group.lift' (λ g : free_group ι,
    (mul_aut.conj g : free_group ι ≃* free_group ι).to_monoid_hom.comp
      (gpowers_hom (free_group ι) r)) w :=
semidirect_product.lift_inl _ _ _ _

omit r

def remove_subscript (t : ι) : free_group (ι × C∞) →* free_group ι :=
free_group.lift' (λ g, (mul_aut.conj (of' t g.2)).to_monoid_hom.comp (of' g.1))

def mul_subscript (n : C∞) : free_group (ι × C∞) ≃* free_group (ι × C∞) :=
free_group.equiv (equiv.prod_congr (equiv.refl _) (mul_left n))

@[simp] lemma remove_subscript_comp_mul_subscript (t : ι) (n : C∞) :
  (remove_subscript t).comp (mul_subscript n).to_monoid_hom =
  (mul_aut.conj (of' t n)).to_monoid_hom.comp (remove_subscript t) :=
free_group.hom_ext (by simp [remove_subscript, mul_subscript, of_eq_of'])

@[simp] lemma remove_subscript_mul_subscript (t : ι) (n : C∞) (x) : remove_subscript t
  (mul_subscript n x) =  of' t n * remove_subscript t x * of' t n⁻¹ :=
by simpa [-remove_subscript_comp_mul_subscript] using monoid_hom.ext_iff.1
  (remove_subscript_comp_mul_subscript t n) x

@[simp] lemma remove_subscript_of' (t : ι) (l : ι × C∞) (n : C∞) : remove_subscript t (of' l n) =
  (mul_aut.conj (of' t l.2)).to_monoid_hom.comp (of' l.1) n :=
free_group.lift'_of' _ _ _

lemma remove_subscript_SD (t : ι) :
  free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞) →*
  free_group (free_group ι) ⋊[phi'] free_group ι :=
semidirect_product.lift (inl.comp
  (free_group.lift' (λ g, of' (remove_subscript t g))))
  (inr.comp (remove_subscript t))
  begin
    intro g,
    apply free_group.hom_ext,
    assume i,
    simp only [of_eq_of', lift'_of', monoid_hom.comp_apply, mul_equiv.to_monoid_hom_apply, phi'_of'],
    apply semidirect_product.ext;
    simp [phi']
  end

include r

/-- Not the correct definition -/
structure solver (T : set ι): Type :=
(to_fun : free_group ι → option (free_group (free_group ι) ⋊[phi'] free_group ι))
(inv : ∀ (x : free_group ι), x ∈ (set.univ : set (free_group ι)) →
  ∃ (y : free_group (free_group ι) ⋊[phi'] free_group ι), y ∈ to_fun x → unnormalize' r y = x)

instance : has_coe_to_fun (solver r T) :=
{ F := λ _, free_group ι → option (free_group (free_group ι) ⋊[phi'] free_group ι),
  coe := solver.to_fun }

lemma unnormalize_eq_of_mem {n : solver r T}
  {x : free_group ι} {y : free_group (free_group ι) ⋊[phi'] free_group ι}
  (h : y ∈ n x) : unnormalize' r y = x := sorry

lemma unnormalize_inl_eq_of_mem {n : solver r T}
  {x : free_group ι} {y : free_group (free_group ι) ⋊[phi'] free_group ι}
  (h : y ∈ n x) : unnormalize' r (inl y.left) = x * y.right⁻¹ :=
by rw [eq_mul_inv_iff_mul_eq, ← unnormalize'_inr r y.right, ← monoid_hom.map_mul,
    inl_left_mul_inr_right, unnormalize_eq_of_mem r T h]

variable {ι}

omit r

noncomputable def normalize_cons
  (t : ι) (r' : free_group (ι × C∞))
  (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) :
  Π (old1 : free_group (ι × C∞))
  (old2 : free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞)),
  free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞)
| old1 ⟨w, ⟨[], _⟩⟩     := ⟨phi' old1 w, old1⟩
| old1 ⟨w, ⟨i :: l, _⟩⟩ :=
  if i.1.1 = t
  then if i.2 ≤ 1
    then option.elim (hA old1)
      (normalize_cons ⟨old1.1 ++ [i], sorry⟩ ⟨(phi' (of' i.1 i.2))⁻¹ w, ⟨l, sorry⟩⟩)
      (λ a, inr (of (t, 1))⁻¹ *
        normalize_cons (mul_subscript ii (right_hom a))
          ⟨phi' (of (t, 1)) (phi' a.right⁻¹ a.left * w), of' i.1 (ii * i.2) * ⟨l, sorry⟩⟩)
    else option.elim (hB old1)
      (normalize_cons ⟨old1.1 ++ [i], sorry⟩ ⟨(phi' (of' i.1 i.2))⁻¹ w, ⟨l, sorry⟩⟩)
      (λ a, inr (of (t, 1)) *
        normalize_cons (mul_subscript (ii⁻¹) (right_hom a))
          ⟨phi' (of (t, 1))⁻¹  (phi' a.right⁻¹ a.left * w), of' i.1 (ii⁻¹ * i.2) *⟨l, sorry⟩⟩)
  else normalize_cons ⟨old1.1 ++ [i], sorry⟩ ⟨(phi' (of' i.1 i.2))⁻¹ w, ⟨l, sorry⟩⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }

@[simp] lemma remove_subscript_unnormalize_normalize_cons
  (t : ι) (r' : free_group (ι × C∞))
  (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A)
  (hB : solver r' B) :
  Π (old1 : free_group (ι × C∞))
  (old2 : free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞)),
  remove_subscript t (unnormalize' r' (normalize_cons t r' A B hA hB old1 old2)) =
    remove_subscript t (old1 * unnormalize' r' old2)
| old1 ⟨w, ⟨[], _⟩⟩     := by rw normalize_cons; simp [inl_aut]
| old1 ⟨w, ⟨i :: l, _⟩⟩ := begin
  rw normalize_cons,
  split_ifs,
  { cases h1 : hA old1,
    { simp [remove_subscript_unnormalize_normalize_cons, inl_aut_inv, mul_assoc] },
    { have : i.1.2 = ii, from sorry,
      simp [remove_subscript_unnormalize_normalize_cons, mul_assoc, inl_aut_inv,
        unnormalize_inl_eq_of_mem _ _ h1, of_eq_of', inl_aut, this, h] } },
  { cases h2 : hB old1,
    { simp [remove_subscript_unnormalize_normalize_cons, inl_aut_inv, mul_assoc] },
    { have : i.1.2 = ii, from sorry,
      simp [remove_subscript_unnormalize_normalize_cons, mul_assoc, inl_aut_inv,
        unnormalize_inl_eq_of_mem _ _ h2, of_eq_of', inl_aut, this, h] } },
  { simp [remove_subscript_unnormalize_normalize_cons, inl_aut_inv, mul_assoc] }
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩], dec_tac := `[trivial] }

noncomputable def normalize_with_subscript_aux
  (t : ι) (r' : free_group (ι × C∞))
  (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) :
  Π (w : list (Σ i : ι, C∞)) (hw : reduced w),
  free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞)
| []       _ := 1
| (i :: l) _ := normalize_cons t r' A B hA hB (of' (i.1, 1) i.2)
  (normalize_with_subscript_aux l sorry)

noncomputable def normalize_with_subscript
  (t : ι) (r' : free_group (ι × C∞))
  (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B)
  (w : free_group ι) :
  free_group (free_group (ι × C∞)) ⋊[phi'] free_group (ι × C∞) :=
normalize_with_subscript_aux t r' A B hA hB w.1 w.2

lemma remove_subscript_unnormalize_normalize_with_subscript_aux
  (t : ι) (r' : free_group (ι × C∞))
  (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) :
  Π (w : list (Σ i : ι, C∞)) (hw : reduced w),
  remove_subscript t (unnormalize' r' (normalize_with_subscript_aux t r' A B hA hB w hw)) = ⟨w, hw⟩
| []       _ := by simp [normalize_with_subscript_aux]
| (i :: l) _ := begin
  rw [normalize_with_subscript_aux, remove_subscript_unnormalize_normalize_cons,
    monoid_hom.map_mul, remove_subscript_unnormalize_normalize_with_subscript_aux],
  simp
end

@[simp] lemma remove_subscript_unnormalize_normalize_with_subscript
  (t : ι) (r' : free_group (ι × C∞)) (A B : set (ι × C∞))
  [decidable_pred A] [decidable_pred B]
  (hA : solver r' A) (hB : solver r' B) (w : free_group ι) :
  remove_subscript t (unnormalize' r' (normalize_with_subscript t r' A B hA hB w)) = w :=
by cases w; apply remove_subscript_unnormalize_normalize_with_subscript_aux

def Icc_prod (x : ι) (a b : C∞) : set (ι × C∞) :=
{ p | p.1 = x → a ≤ p.2 ∧ p.2 ≤ b }

instance (x : ι) (a b : C∞) : decidable_pred (Icc_prod x a b) :=
by dunfold Icc_prod; apply_instance

def normalize (t x : ι) (r' : free_group (ι × ℤ))
  (hx : x ∉ T) (ht : exp_sum t r = 1) (a b : ℤ)
  (ha : a ∈ finset.min ((vars r').image prod.snd))
  (hb : b ∈ finset.max ((vars r').image prod.snd))
  (hr' : r' = ((free_group.to_SD t) r).left)
  (hr'₁ : solver r' (Icc_prod x a (b * ii⁻¹)))
  (hr'₂ : solver r' (Icc_prod x (a * ii) b)) :
  solver r T :=



