import .basic

universes u v

variables (M N : Type u) [monoid M] [monoid N]
variables (G H : Type u) [group G] [group H]
variables {K : Type v} [monoid K]

def bicoprod_monoid_aux (b : bool) : monoid (cond b M N) :=
{ mul := bool.cases_on b ((*) : N → N → N) ((*) : M → M → M),
  one := bool.cases_on b (1 : N) (1 : M),
  mul_assoc := bool.cases_on b (@mul_assoc N _) (@mul_assoc M _),
  one_mul := bool.cases_on b (@one_mul N _) (@one_mul M _),
  mul_one := bool.cases_on b (@mul_one N _) (@mul_one M _) }

local attribute [instance] bicoprod_monoid_aux

def bicoprod := coprod (λ b : bool, cond b M N)

namespace bicoprod

variables [decidable_eq M] [decidable_eq N] [decidable_eq G] [decidable_eq H]

infixr ` ⋆ `: 30 := bicoprod

def bicoprod_group_aux (b : bool) :
  group (cond b G H) :=
let I : group (cond b G H) := by cases b; dunfold cond; apply_instance in
{ inv := bool.cases_on b (@has_inv.inv H _) (@has_inv.inv G _),
  mul_left_inv := bool.cases_on b (@mul_left_inv H _) (@mul_left_inv G _),
  ..bicoprod_monoid_aux G H b }

def bicoprod_dec_eq_aux (b : bool) :
  decidable_eq (cond b M N) := by cases b; dunfold cond; apply_instance

local attribute [instance] bicoprod_group_aux bicoprod_dec_eq_aux

instance : monoid (M ⋆ N) := coprod.monoid

instance : group (G ⋆ H) := @coprod.group bool (λ b, cond b G H) _ _ _

variables {M N}

def inl : M →* M ⋆ N :=
{ to_fun := @coprod.of bool (λ b, cond b M N) _ _ _ tt,
  map_one' := by simp,
  map_mul' := by simp }

def inr : N →* M ⋆ N :=
{ to_fun := @coprod.of bool (λ b, cond b M N) _ _ _ ff,
  map_one' := by simp,
  map_mul' := by simp }

def lift (f : M →* K) (g : N →* K) : M ⋆ N →* K :=
{ to_fun := coprod.lift (λ b, show cond b M N →* K,
    from bool.rec_on b ⟨g, by simp, by simp⟩ ⟨f, by simp, by simp⟩ ),
  map_one' := by simp,
  map_mul' := by simp }

@[simp] lemma lift_inl (f₁ : M →* K) (f₂ : N →* K) (m : M) :
  (lift f₁ f₂) (inl m) = f₁ m :=
@coprod.lift_of bool (λ b, cond b M N) _ _ _ _ _ _ tt m

@[simp] lemma lift_inr (f₁ : M →* K) (f₂ : N →* K) (n : N) :
  (lift f₁ f₂) (inr n) = f₂ n :=
@coprod.lift_of bool (λ b, cond b M N) _ _ _ _ _ _ ff n

@[simp] lemma lift_comp_inl (f₁ : G →* M) (f₂ : H →* M) :
  (lift f₁ f₂).comp inl = f₁ :=
monoid_hom.ext (lift_inl _ _)

@[simp] lemma lift_comp_inr (f₁ : G →* M) (f₂ : H →* M) :
  (lift f₁ f₂).comp inr = f₂ :=
monoid_hom.ext (lift_inr _ _)

end bicoprod
