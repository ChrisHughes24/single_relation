/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.equiv.mul_add logic.function.basic group_theory.subgroup
/-!
# Semidirect product

This file defines semidirect products of groups, and the canonical maps in and out of the
semidirect product. The semidirect product of `N` and `G` given a hom `φ` from
`φ` from `G` to the automorphism group of `N` is the product of sets with the group
`⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩`

## Key definitions

There are two homs into the semidirect product `inl : N →* G ⋉[φ] N` and
`inr : G →* G ⋉[φ] N`, and `lift` can be used to define maps `G ⋉[φ] N →* H`
out of the semidirect product given maps `f₁ : N →* H` and `f₂ : G →* H` that satisfy the
condition `∀ n g, f₁ (φ g n) = f₂ g * f₁ n * f₂ g⁻¹`

## Notation

This file introduces the global notation `G ⋉[φ] N` for `semidirect_product N G φ`

## Tags
group, semidirect product
-/
variables (G : Type*) (N : Type*) {H : Type*} [group N] [group G] [group H]

/-- The semidirect product of groups `N` and `G`, given a map `φ` from `G` to the automorphism
  group of `N`. It the product of sets with the group operation
  `⟨n₁, g₁⟩ * ⟨n₂, g₂⟩ = ⟨n₁ * φ g₁ n₂, g₁ * g₂⟩` -/
@[ext, derive decidable_eq]
structure lsemidirect_product (φ : G →* mul_aut N) :=
(left : G) (right : N)

attribute [pp_using_anonymous_constructor] lsemidirect_product

notation G` ⋉[`:35 φ:35`] `:0 N :35 := lsemidirect_product G N φ

namespace lsemidirect_product

variables {N G} {φ : G →* mul_aut N}

private def one_aux : G ⋉[φ] N := ⟨1, 1⟩
private def mul_aux (a b : G ⋉[φ] N) : G ⋉[φ] N := ⟨a.left * b.left, φ b.1⁻¹ a.2 * b.2⟩
private def inv_aux (a : G ⋉[φ] N) : G ⋉[φ] N := ⟨a.1⁻¹, φ a.1 a.2⁻¹⟩
private lemma mul_assoc_aux (a b c : G ⋉[φ] N) : mul_aux (mul_aux a b) c = mul_aux a (mul_aux b c) :=
by simp [mul_aux, mul_assoc, mul_equiv.map_mul]
private lemma mul_one_aux (a : G ⋉[φ] N) : mul_aux a one_aux = a :=
by cases a; simp [mul_aux, one_aux]
private lemma one_mul_aux (a : G ⋉[φ] N) : mul_aux one_aux a = a :=
by cases a; simp [mul_aux, one_aux]
private lemma mul_left_inv_aux (a : G ⋉[φ] N) : mul_aux (inv_aux a) a = one_aux :=
by simp only [mul_aux, inv_aux, one_aux, ← mul_equiv.map_mul, mul_left_inv]; simp; admit

instance : group (G ⋉[φ] N) :=
{ one := one_aux,
  inv := inv_aux,
  mul := mul_aux,
  mul_assoc := mul_assoc_aux,
  one_mul := one_mul_aux,
  mul_one := mul_one_aux,
  mul_left_inv := mul_left_inv_aux }

instance : inhabited (G ⋉[φ] N) := ⟨1⟩

@[simp] lemma one_left : (1 : G ⋉[φ] N).left = 1 := rfl
@[simp] lemma one_right : (1 : G ⋉[φ] N).right = 1 := rfl
@[simp] lemma inv_left (a : G ⋉[φ] N) : (a⁻¹).left = a.left⁻¹ := rfl
@[simp] lemma inv_right (a : G ⋉[φ] N) : (a⁻¹).right = φ a.left a.right⁻¹ := rfl
@[simp] lemma mul_left (a b : G ⋉[φ] N) : (a * b).left = a.left * b.left := rfl
@[simp] lemma mul_right (a b : G ⋉[φ] N) : (a * b).right = φ b.left⁻¹ a.right * b.right := rfl

/-- The canonical map `N →* G ⋉[φ] N` sending `n` to `⟨n, 1⟩` -/
def inl : G →* G ⋉[φ] N :=
{ to_fun := λ g, ⟨g, 1⟩,
  map_one' := rfl,
  map_mul' := by intros; ext; simp }

@[simp] lemma left_inl (g : G) : (inl g : G ⋉[φ] N).left = g := rfl
@[simp] lemma right_inl (g : G) : (inl g : G ⋉[φ] N).right = 1 := rfl

lemma inl_injective : function.injective (inl : G → G ⋉[φ] N) :=
function.injective_iff_has_left_inverse.2 ⟨left, left_inl⟩

@[simp] lemma inl_inj {g₁ g₂ : G} : (inl g₁ : G ⋉[φ] N) = inl g₂ ↔ g₁ = g₂ :=
inl_injective.eq_iff

/-- The canonical map `G →* G ⋉[φ] N` sending `g` to `⟨1, g⟩` -/
def inr : N →* G ⋉[φ] N :=
{ to_fun := λ n, ⟨1, n⟩,
  map_one' := rfl,
  map_mul' := by intros; ext; simp }

@[simp] lemma left_inr (n : N) : (inr n : G ⋉[φ] N).left = 1 := rfl
@[simp] lemma right_inr (n : N) : (inr n : G ⋉[φ] N).right = n := rfl

lemma inr_injective : function.injective (inr : N → G ⋉[φ] N) :=
function.injective_iff_has_left_inverse.2 ⟨right, right_inr⟩

@[simp] lemma inr_inj {n₁ n₂ : N} : (inr n₁ : G ⋉[φ] N) = inr n₂ ↔ n₁ = n₂ :=
inr_injective.eq_iff

lemma inr_aut (g : G) (n : N) : (inr (φ g n) : G ⋉[φ] N) = inl g * inr n * inl g⁻¹ :=
by ext; simp

lemma inl_aut_inv (g : G) (n : N) : (inr ((φ g)⁻¹ n) : G ⋉[φ] N) = inl g⁻¹ * inr n * inl g :=
by rw [← monoid_hom.map_inv, inr_aut, inv_inv]

lemma inl_left_mul_inr_right (x : G ⋉[φ] N) : inl x.left * inr x.right = x :=
by ext; simp

/-- The canonical projection map `G ⋉[φ] N →* G`, as a group hom. -/
def left_hom : G ⋉[φ] N →* G :=
{ to_fun := lsemidirect_product.left,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

@[simp] lemma left_hom_eq_left : (left_hom :  G ⋉[φ] N → G) = left := rfl

@[simp] lemma left_hom_comp_inr : (left_hom : G ⋉[φ] N →* G).comp inr = 1 :=
by ext; simp [left_hom]

@[simp] lemma right_hom_comp_inl : (left_hom : G ⋉[φ] N →* G).comp inl = monoid_hom.id _ :=
by ext; simp [left_hom]

@[simp] lemma left_hom_inr (n : N) : left_hom (inr n : G ⋉[φ] N) = 1 :=
by simp [left_hom]

@[simp] lemma left_hom_inl (g : G) : left_hom (inl g : G ⋉[φ] N) = g :=
by simp [left_hom]

lemma left_hom_surjective : function.surjective (left_hom : G ⋉[φ] N → G) :=
function.surjective_iff_has_right_inverse.2 ⟨inl, left_hom_inl⟩

lemma range_inr_eq_ker_left_hom : (inr : N →* G ⋉[φ] N).range = left_hom.ker :=
le_antisymm
  (λ _, by simp [monoid_hom.mem_ker, eq_comm] {contextual := tt})
  (λ x hx, ⟨x.right, by ext; simp [*, monoid_hom.mem_ker] at *⟩)

section lift
variables (f₁ : N →* H) (f₂ : G →* H)
  (h : ∀ g, f₁.comp (φ g).to_monoid_hom = (mul_aut.conj (f₂ g)).to_monoid_hom.comp f₁)

/-- Define a group hom `G ⋉[φ] N →* H`, by defining maps `N →* H` and `G →* H`  -/
def lift  (f₁ : G →* H) (f₂ : N →* H)
  (h : ∀ g, f₂.comp (φ g).to_monoid_hom = (mul_aut.conj (f₁ g)).to_monoid_hom.comp f₂) :
  G ⋉[φ] N →* H :=
{ to_fun := λ a, f₁ a.1 * f₂ a.2,
  map_one' := by simp,
  map_mul' := λ a b, begin
    have := λ n g, monoid_hom.ext_iff.1 (h n) g,
    simp only [mul_aut.conj_apply, monoid_hom.comp_apply, mul_equiv.to_monoid_hom_apply] at this,
    simp [this, mul_assoc],
  end }

@[simp] lemma lift_inl (n : N) : lift f₁ f₂ h (inl n) = f₁ n := by simp [lift]
@[simp] lemma lift_comp_inl : (lift f₁ f₂ h).comp inl = f₁ := by ext; simp

@[simp] lemma lift_inr (g : G) : lift f₁ f₂ h (inr g) = f₂ g := by simp [lift]
@[simp] lemma lift_comp_inr : (lift f₁ f₂ h).comp inr = f₂ := by ext; simp

lemma left_mul_right (x : G ⋉[φ] N) :
  inl x.left * inr x.right = x := by ext; simp

lemma lift_unique (F : G ⋉[φ] N →* H) :
  F = lift (F.comp inl) (F.comp inr) (λ _, by ext; simp [inl_aut]) :=
begin
  ext,
  simp only [lift, monoid_hom.comp_apply, monoid_hom.coe_mk],
  rw [← F.map_mul, inl_left_mul_inr_right],
end

end lift

end lsemidirect_product
