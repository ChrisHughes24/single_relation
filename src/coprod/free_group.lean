import coprod.basic
import data.int.basic
import algebra.group_power
import logic.embedding
import data.equiv.mul_add
import group_theory.subgroup

notation `C∞` := multiplicative ℤ

@[reducible] def free_group (ι : Type*) := coprod (λ i : ι, C∞)

namespace free_group
variables {ι : Type*} [decidable_eq ι] {M : Type*} [monoid M] {G : Type*} [group G]
variables {α : Type*} {β : Type*} {γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

open function coprod coprod.pre multiplicative

instance : group (free_group ι) := @coprod.group ι (λ i : ι, C∞) _ _ _
instance : decidable_eq (free_group ι) := coprod.decidable_eq

def of (i : ι) : free_group ι := ⟨[⟨i, of_add 1⟩], reduced_singleton dec_trivial⟩

def of' (i : ι) : C∞ →* free_group ι := coprod.of i

def length : free_group α → ℕ :=
λ w, (w.to_list.map (λ a : Σ i : α, C∞, a.2.to_add.nat_abs)).sum

@[simp] lemma cons_eq_of'_mul (l : list (Σ i : ι, C∞))
  (g : Σ i : ι, C∞) (h) :
  @eq (free_group ι) ⟨g :: l, h⟩ (of' g.1 g.2 * ⟨l, reduced_of_reduced_cons h⟩) :=
coprod.cons_eq_of_mul _ _

@[simp] lemma append_eq_mul {l₁ l₂ : list (Σ i : ι, C∞)} (hl : reduced (l₁ ++ l₂)) :
  @eq (free_group ι) ⟨l₁ ++ l₂, hl⟩ (⟨l₁, reduced_of_reduced_append_left hl⟩ *
    ⟨l₂, reduced_of_reduced_append_right hl⟩) :=
coprod.append_eq_mul _

lemma of'_eq_of_pow (i : ι) (n : C∞) : of' i n = (of i) ^ n.to_add :=
calc of' i n = gpowers_hom _ (of i) n : congr_fun (congr_arg _ (monoid_hom.ext_int rfl)) _
... = _ : rfl

@[simp] lemma nil_eq_one (h): @eq (free_group ι) ⟨[], h⟩ 1 := rfl

@[simp] lemma eta (w : free_group ι) : (⟨w.1, w.2⟩ : free_group ι) = w := by cases w; refl

lemma of_eq_of' (i : ι) : of i = of' i (of_add 1) := rfl

def lift' (f : Π i : ι, C∞ →* M) : free_group ι →* M :=
coprod.lift f

def lift (f : ι → G) : free_group ι →* G :=
lift' (λ i, gpowers_hom _ (f i))

@[simp] lemma lift'_of' (f : Π i : ι, C∞ →* M) (i : ι) (n : C∞) :
  lift' f (of' i n) = f i n := by simp [lift', of']

@[simp] lemma lift_of (f : Π i : ι, G) (i : ι) :
  lift f (of i) = f i := by simp [lift, of_eq_of', gpowers_hom]

@[simp] lemma lift'_comp_of' (f : Π i : ι, C∞ →* M) (i : ι) :
  (lift' f).comp (of' i) = f i := by ext; simp

@[elab_as_eliminator]
def rec_on' {C : free_group ι → Prop}
  (g : free_group ι)
  (h1 : C 1)
  (hof : ∀ i n, C (of' i n))
  (f : Π (i : ι) (n : C∞) (h : free_group ι), C (of' i n) → C h → C (of' i n * h)) : C g :=
coprod.rec_on g h1 hof f

@[elab_as_eliminator]
lemma rec_on {C : free_group ι → Prop}
  (g : free_group ι)
  (h1 : C (1 : free_group ι))
  (hof : ∀ i, C (of i))
  (hinv : ∀ i, C ((of i)⁻¹))
  (hmul : Π (a b : free_group ι), C a → C b → C (a * b)) :
  C g :=
free_group.rec_on' g h1 (begin
  assume i n,
  refine int.induction_on n _ _ _,
  { change (0 : ℤ) with (1 : C∞), simpa },
  { assume n h,
    change (n + 1 : ℤ) with (of_add (n + 1 : ℤ)),
    rw [of_add_add, monoid_hom.map_mul],
    exact hmul _ _ h (hof _) },
  { assume n h,
    change (-n - 1 : ℤ) with (of_add (-n - 1 : ℤ)),
    erw [sub_eq_add_neg, of_add_add, of_add_neg, of_add_neg,
      monoid_hom.map_mul, monoid_hom.map_inv (of' i) (of_add 1), ← of_eq_of'],
    exact hmul _ _ h (hinv _) },
end)
(λ i a h , hmul _ _)

lemma hom_ext {f g : free_group ι →* M} (h : ∀ i, f (of i) = g (of i)) : f = g :=
coprod.hom_ext (λ i, monoid_hom.ext_int (h i))

@[simp] lemma lift_of₂ : lift (of : ι → free_group ι) = monoid_hom.id _ :=
free_group.hom_ext (by simp)

lemma lift'_eq_lift (f : Π i : ι, C∞ →* G) : lift' f = lift (λ i, f i (of_add 1)) :=
hom_ext (λ i, by rw [lift_of, of_eq_of', lift'_of'])

section map

variables {κ : Type*} [decidable_eq κ] (f : ι → κ)

def map : free_group ι →* free_group κ := lift' (λ i, of' (f i))

@[simp] lemma map_of (i : ι): map f (of i) = of (f i) := by simp [map, of_eq_of']

@[simp] lemma map_of' (i : ι) (n : C∞) : map f (of' i n) = of' (f i) n :=
by simp [map, of_eq_of']

@[simp] lemma map_comp_of' (i : ι) : (map f).comp (of' i) = of' (f i) :=
by simp [map, of_eq_of']

lemma lift_comp_map (g : κ → G) : (lift g).comp (map f) = lift (λ x, g (f x)) :=
hom_ext (by simp)

lemma lift_map (g : κ → G) (w : free_group ι) : lift g (map f w) = lift (λ x, g (f x)) w :=
by rw [← monoid_hom.comp_apply, lift_comp_map]

@[simp] lemma map_id : map (λ x, x : ι → ι) = monoid_hom.id _ :=
free_group.hom_ext (by simp [map, of_eq_of'])

end map

protected def embedding (e : α ↪ β) : free_group α →* free_group β :=
{ to_fun := λ x, ⟨pre.embedding e.1 (λ _, monoid_hom.id _) x.1,
    pre.reduced_embedding _ e.2 _ (by simp) x.2⟩,
  map_one' := rfl,
  map_mul' := λ _ _, subtype.eq (by dsimp; exact pre.embedding_mul e.1 e.2
    (λ _, monoid_hom.id _) (by simp)) }

@[simp] lemma embedding_of' (e : α ↪ β) (a : α) (n : C∞) :
  free_group.embedding e (of' a n) = of' (e a) n :=
subtype.eq begin
  simp [free_group.embedding, of', coprod.of, coprod.pre.of, pre.embedding],
  split_ifs; simp
end

@[simp] lemma embedding_of (e : α ↪ β) (a : α) :
  free_group.embedding e (of a) = of (e a) :=
by simp [of_eq_of']

@[simp] lemma embedding_id : free_group.embedding (embedding.refl α) = monoid_hom.id _ :=
free_group.hom_ext (λ _, by simp)

@[simp] lemma embedding_trans (e₁ : α ↪ β) (e₂ : β ↪ γ) :
  free_group.embedding (e₁.trans e₂) = (free_group.embedding e₂).comp (free_group.embedding e₁) :=
free_group.hom_ext (λ _, by simp)

protected def equiv (e : α ≃ β) : free_group α ≃* free_group β :=
{ to_fun := free_group.embedding e.to_embedding,
  inv_fun := free_group.embedding e.symm.to_embedding,
  left_inv := λ x, begin
      rw [← monoid_hom.comp_apply],
      conv_rhs { rw ← monoid_hom.id_apply x },
      refine congr_fun (congr_arg _ (free_group.hom_ext (by simp))) _
    end,
  right_inv := λ x, begin
      rw [← monoid_hom.comp_apply],
      conv_rhs { rw ← monoid_hom.id_apply x },
      refine congr_fun (congr_arg _ (free_group.hom_ext (by simp))) _
    end,
  map_mul' := by simp }

@[simp] lemma equiv_refl : free_group.equiv (equiv.refl α) = mul_equiv.refl _ :=
by ext; simp [free_group.equiv]

@[simp] lemma equiv_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
  free_group.equiv (e₁.trans e₂) = (free_group.equiv e₁).trans (free_group.equiv e₂) :=
by ext; simp [free_group.equiv]

@[simp] lemma equiv_of' (e : α ≃ β) (a : α) (n : C∞) :
  free_group.equiv e (of' a n) = of' (e a) n :=
by ext; simp [free_group.equiv]

@[simp] lemma equiv_of (e : α ≃ β) (a : α) :
  free_group.equiv e (of a) = of (e a) :=
by simp [free_group.equiv]

def exp_sum (i : ι) : free_group ι →* C∞ :=
free_group.lift' (λ j, if i = j then monoid_hom.id _ else 1)

@[simp] def exp_sum_of' (t i : ι) (n : C∞) : exp_sum t (of' i n) = if t = i then n else 1 :=
by simp [exp_sum]; split_ifs; simp

@[simp] def exp_sum_of (t i : ι) : exp_sum t (of i) = if t = i then of_add (1 : ℤ) else 1 :=
by simp [exp_sum]; split_ifs; simp [of_eq_of', *]

end free_group
