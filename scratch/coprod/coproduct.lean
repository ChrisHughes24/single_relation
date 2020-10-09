import tactic.equiv_rw tactic group_theory.subgroup group_theory.semidirect_product

universes u v w x y z

def mul_left {G : Type*} [group G] : G →* equiv.perm G :=
{ to_fun := λ g,
  { to_fun := λ h, g * h,
    inv_fun := λ h, g⁻¹ * h,
    left_inv := λ _, by simp [mul_assoc],
    right_inv := λ _, by simp [mul_assoc] },
  map_one' := by ext; simp,
  map_mul' := λ _ _, by ext; simp [mul_assoc] }

@[simp] lemma coe_fn_mul_left {G : Type*} [group G] (g : G) : (⇑(mul_left g) : G → G) = (*) g := rfl
@[simp] lemma coe_fn_mul_left_symm {G : Type*} [group G] (g : G) : (⇑(mul_left g).symm : G → G) = (*) g⁻¹ := rfl

noncomputable theory

def reduced  {ι : Type u} {G : ι → Type v} [Π i, group (G i)] (l : list (Σ i : ι, G i)) : Prop :=
l.chain' (λ a b, a.1 ≠ b.1) ∧ ∀ a : Σ i, G i, a ∈ l → a.2 ≠ 1

def coprod {ι : Type u} (G : ι → Type v) [Π i, group (G i)] : Type (max u v) :=
{ l : list (Σ i, G i) // reduced l }

--protected constant coprod.monoid [Π i, monoid (G i)] : monoid (coprod G)
protected constant coprod.group {ι : Type u} {G : ι → Type v} [Π i, group (G i)] : group (coprod G)
attribute [instance] coprod.group

namespace coprod

variables {ι : Type u} [decidable_eq ι] {G : ι → Type v} [Π i, group (G i)] {M : Type w}
variables {α : Type*} {β : Type*} {γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

constant of : Π i : ι, G i →* coprod G

@[simp] lemma cons_eq_of_mul {l : list (Σ i, G i)}
  (g : Σ i , G i) (h) :
  @eq (coprod G) (⟨g :: l, h⟩ : coprod G) (of g.1 g.2 * ⟨l, sorry⟩) := sorry

@[simp] lemma append_eq_mul (l₁ l₂ : list (Σ i, G i)) (hl):
  @eq (coprod G) ⟨l₁ ++ l₂, hl⟩ (⟨l₁, sorry⟩ * ⟨l₂, sorry⟩) := sorry

@[simp] lemma eta (w : coprod G) : (⟨w.1, w.2⟩ : coprod G) = w := by cases w; refl

constant lift [monoid M] (f : Π i, G i →* M) : coprod G →* M

protected constant decidable_eq : decidable_eq (coprod G)

attribute [instance] coprod.decidable_eq

@[simp] lemma lift_of [monoid M] (f : Π i, G i →* M) {i : ι} (g : G i) :
  lift f (of i g) = f i g := sorry

@[simp] lemma lift_comp_of [monoid M] (f : Π i, G i →* M) (i : ι) :
  (lift f).comp (of i) = f i :=
by ext; simp

@[elab_as_eliminator]
constant rec_on {C : coprod G → Sort*} (g : coprod G) (h1 : C 1)
  (f : Π (g : Σ i, G i) (h : coprod G), C h → C (of g.1 g.2 * h)) : C g

@[simp] lemma rec_on_one {C : coprod G → Sort*} (h1 : C 1)
  (f : Π (g : Σ i, G i) (h : coprod G), C h → C (of g.1 g.2 * h)) :
  (rec_on (1 : coprod G) h1 f : C 1) = h1 := sorry

lemma rec_on_mul {C : coprod G → Sort*} {i j : ι} (hij : i ≠ j)
  (g : G i) (h : G j) (x : coprod G) (hg1 : g ≠ 1) (hh1 : h ≠ 1)
  (h1 : C 1) (f : Π (g : Σ i, G i) (h : coprod G), C h → C (of g.1 g.2 * h)) :
  (rec_on (of i g * (of j h * x)) h1 f : C (of i g * (of j h * x))) =
  f ⟨i, g⟩ (of j h * x) (rec_on (of j h * x) h1 f) := sorry

lemma hom_ext [monoid M] {f g : coprod G →* M}
  (h : ∀ i : ι, f.comp (of i) = g.comp (of i)) : f = g :=
begin
  ext,
  refine coprod.rec_on x _ _,
  { simp },
  { rintros ⟨i, k⟩ x hfg,
    have := monoid_hom.ext_iff.1 (h i) k,
    erw [monoid_hom.map_mul, monoid_hom.map_mul, this, hfg], dsimp, refl, }
end

lemma mul_equiv_ext [monoid M] {f g : coprod G ≃* M}
  (h : ∀ i : ι, f.to_monoid_hom.comp (of i) = g.to_monoid_hom.comp (of i)) :
  f = g :=
sorry

end coprod

notation `C∞` := multiplicative ℤ

def ii : C∞ := show ℤ, from 1

def free_group (ι : Type*) := coprod (λ i : ι, multiplicative ℤ)

namespace free_group
variables {ι : Type u} [decidable_eq ι] {M : Type w}
variables {α : Type*} {β : Type*} {γ : Type*} [decidable_eq α] [decidable_eq β] [decidable_eq γ]

open function

instance : group (free_group ι) := coprod.group
instance : decidable_eq (free_group ι) := coprod.decidable_eq

def of (i : ι) : free_group ι := coprod.of i ii

def of' (i : ι) : multiplicative ℤ →* free_group ι := coprod.of i

@[simp] lemma cons_eq_of'_mul (l : list (Σ i : ι, multiplicative ℤ))
  (g : Σ i : ι, multiplicative ℤ) (h) :
  @eq (free_group ι) ⟨g :: l, h⟩ (of' g.1 g.2 * ⟨l, sorry⟩) :=
sorry

lemma of'_eq_pow (i : ι) (n : C∞) : of' i n = (of i) ^ n.to_add := sorry

@[simp] lemma append_eq_mul (l₁ l₂ : list (Σ i : ι, multiplicative ℤ)) (hl):
  @eq (free_group ι) ⟨l₁ ++ l₂, hl⟩ (⟨l₁, sorry⟩ * ⟨l₂, sorry⟩) := sorry

@[simp] lemma nil_eq_one : @eq (free_group ι) ⟨[], sorry⟩ 1 := sorry

-- @[simp] lemma cons_eq_of'_mul' (l : list (Σ i : ι, multiplicative ℤ))
--   (hl : reduced l) (g : multiplicative ℤ) (h) :
-- (⟨⟨i, g⟩ :: l, h⟩ : free_group ι) = @has_mul.mul (free_group ι) _ (of' i g) ⟨l, hl⟩ := sorry

@[simp] lemma eta (w : free_group ι) : (⟨w.1, w.2⟩ : free_group ι) = w := by cases w; refl

lemma of_eq_of' (i : ι) : of i = of' i ii := rfl

def lift' [monoid M] (f : Π i : ι, multiplicative ℤ →* M) : free_group ι →* M :=
coprod.lift f

def lift [group M] (f : ι → M) : free_group ι →* M :=
lift' (λ i, gpowers_hom _ (f i))

@[simp] lemma lift'_of' [monoid M] (f : Π i : ι, multiplicative ℤ →* M) (i : ι) (n : multiplicative ℤ) :
  lift' f (of' i n) = f i n := by simp [lift', of']

@[simp] lemma lift_of [group M] (f : Π i : ι, M) (i : ι) :
  lift f (of i) = f i := by simp [lift, of_eq_of', gpowers_hom, ii,
    multiplicative.to_add]

@[simp] lemma lift'_comp_of' [monoid M] (f : Π i : ι, multiplicative ℤ →* M) (i : ι) :
  (lift' f).comp (of' i) = f i := by ext; simp

@[elab_as_eliminator]
def rec_on' {C : free_group ι → Sort*} (g : free_group ι) (h1 : C 1)
  (f : Π (g : Σ i, multiplicative ℤ) (h : free_group ι), C h → C (of' g.1 g.2 * h)) : C g :=
by exact coprod.rec_on g h1 f

@[simp] lemma rec_on'_one {C : free_group ι → Sort*} (h1 : C 1)
  (f : Π (g : Σ i : ι, multiplicative ℤ) (h : free_group ι), C h → C (of' g.1 g.2 * h)) :
  (rec_on' (1 : free_group ι) h1 f : C 1) = h1 := coprod.rec_on_one h1 f

lemma rec_on'_mul {C : free_group ι → Sort*} {i j : ι} (hij : i ≠ j)
  (g h : ℤ) (x : free_group ι) (hg0 : g ≠ 0) (hh0 : h ≠ 0) (h1 : C 1)
  (f : Π (g : Σ i : ι, multiplicative ℤ) (h : free_group ι), C h → C (of' g.1 g.2 * h)) :
  (rec_on' (of' i g * (of' j h * x)) h1 f : C (of' i g * (of' j h * x))) =
  f ⟨i, g⟩ (of' j h * x) (rec_on' (of' j h * x) h1 f) :=
coprod.rec_on_mul hij g h x hg0 hh0 h1 f

@[elab_as_eliminator]
def rec_on {C : free_group ι → Sort*} (g : free_group ι) (h1 : C 1)
  (f : Π (i : ι) (h : free_group ι), C h → C (of i * h)) : C g :=
sorry

protected constant embedding (e : α ↪ β) : free_group α →* free_group β

@[simp] lemma embedding_id : free_group.embedding (embedding.refl α) = monoid_hom.id _ := sorry

@[simp] lemma embedding_trans (e₁ : α ↪ β) (e₂ : β ↪ γ) :
  free_group.embedding (e₁.trans e₂) = (free_group.embedding e₂).comp (free_group.embedding e₁) := sorry

@[simp] lemma embedding_of' (e : α ↪ β) (a : α) (n : multiplicative ℤ) :
  free_group.embedding e (of' a n) = of' (e a) n := sorry

protected constant equiv (e : α ≃ β) : free_group α ≃* free_group β

@[simp] lemma equiv_refl : free_group.equiv (equiv.refl α) = mul_equiv.refl _ := sorry

@[simp] lemma equiv_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
  free_group.equiv (e₁.trans e₂) = (free_group.equiv e₁).trans (free_group.equiv e₂) := sorry

@[simp] lemma equiv_of' (e : α ≃ β) (a : α) (n : multiplicative ℤ) :
  free_group.equiv e (of' a n) = of' (e a) n := sorry

lemma hom_ext [monoid M] {f g : free_group ι →* M}
  (h : ∀ i, f (of i) = g (of i)) : f = g :=
coprod.hom_ext (λ i, monoid_hom.ext (λ x, sorry))

lemma mul_equiv_ext [monoid M] {f g : free_group ι ≃* M}
  (h : ∀ i, f (of i) = g (of i)) : f = g :=
sorry

def exp_sum (i : ι) : free_group ι →* multiplicative ℤ :=
free_group.lift' (λ j, if i = j then monoid_hom.id _ else 1)

/-- `closure_var` is the group closure of a set of variables -/
def closure_var (T : set ι) : subgroup (free_group ι) :=
subgroup.closure (of '' T)

instance (T : set ι) [decidable_pred T] (g : free_group ι) : decidable (g ∈ closure_var T) := sorry

constant vars (w : free_group ι) : finset ι

end free_group

variables (G H : Type u) [group G] [group H] {M : Type*} [monoid M]

def bicoprod_group_aux (b : bool) :
  group (cond b G H) := by cases b; dunfold cond; apply_instance

local attribute [instance] bicoprod_group_aux

def bicoprod := coprod (λ b : bool, cond b G H)

namespace bicoprod

infixr ` ⋆ `: 30 := bicoprod

instance : group (G ⋆ H) := coprod.group

variables {G H}

def inl : G →* G ⋆ H :=
@coprod.of bool _ (λ b, cond b G H) _ tt

def inr : H →* G ⋆ H :=
@coprod.of bool _ (λ b, cond b G H) _ ff

def lift (f : G →* M) (g : H →* M) : G ⋆ H →* M :=
coprod.lift (λ b, bool.rec_on b g f)

@[simp] lemma lift_comp_inl (f₁ : G →* M) (f₂ : H →* M) :
  (lift f₁ f₂).comp inl = f₁ := coprod.lift_comp_of _ _

@[simp] lemma lift_comp_inr (f₁ : G →* M) (f₂ : H →* M) :
  (lift f₁ f₂).comp inr = f₂ := coprod.lift_comp_of _ _

@[simp] lemma lift_inl (f₁ : G →* M) (f₂ : H →* M) (g : G) :
  (lift f₁ f₂) (inl g) = f₁ g := coprod.lift_of _ _

@[simp] lemma lift_inr (f₁ : G →* M) (f₂ : H →* M) (h : H) :
  (lift f₁ f₂) (inr h) = f₂ h := coprod.lift_of _ _

end bicoprod
