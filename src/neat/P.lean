import group_theory.semidirect_product
import for_mathlib.coprod.free_group
/-!
# The P functor

Given a group `G` an element `p` of the group `P G` can be used as a certificate
of congruences modulo `r : G` in `G`. There are two surjective maps `P G →* G`,
`lhs r` and `right`. `lhs r p` and `right p` will always be congruent modulo
`r` in `G`, and so `p` is a certificate of this congruence. This is used is the
`group_thingy` tactic.
-/

variables {G : Type} [group G] [decidable_eq G]
variables {H : Type} [group H] [decidable_eq H]

open free_group semidirect_product function

lemma to_monoid_hom_inj' {M N : Type*} [monoid M] [monoid N] :
  function.injective (mul_equiv.to_monoid_hom : (M ≃* N) → (M →* N)) :=
λ f g h, mul_equiv.ext (monoid_hom.ext_iff.1 h)

/-- `mul_free` is the extension of the left regular action of `G` to an
  action of `G` on `free_group G` -/
def mul_free : G →* mul_aut (free_group G) :=
{ to_fun := λ g, free_group.equiv (equiv.mul_left g),
  map_mul' := λ _ _, to_monoid_hom_inj' $ free_group.hom_ext $
    by simp [mul_aut.mul_def, equiv.perm.mul_def, mul_assoc],
  map_one' := to_monoid_hom_inj' $ free_group.hom_ext $
    by simp [mul_aut.mul_def, equiv.perm.mul_def, mul_assoc] }

@[simp] lemma mul_free_of' (g : G) (h : G) (n : C∞) :
  mul_free g (of' h n) = of' (g * h) n :=
by simp [mul_free]

@[simp] lemma mul_free_of (g : G) (h : G) : mul_free g (of h) = of (g * h) :=
by simp [mul_free, of_eq_of']

@[simp] lemma mul_free_inv_of (g : G) (h : G) : (mul_free g)⁻¹ (of h) = of (g⁻¹ * h) :=
by rw [← monoid_hom.map_inv, mul_free_of]

variable (G)

/-- The group `P G` is used as a certificate of congruences of elements of `G`
  modulo a relation `r : G`. -/
@[reducible] def P : Type* := free_group G ⋊[mul_free] G

instance [decidable_eq G] : decidable_eq (P G) :=
semidirect_product.decidable_eq _ _ _

variable {G}
namespace P

variables {r : G}

instance : group (P G) := semidirect_product.group

/-- `p` is a certificate of the congruence between `lhs r p` and `right p` modulo `r`  -/
def lhs (r : G) : P G →* G :=
semidirect_product.lift (free_group.lift (λ g, mul_aut.conj g r))
  (monoid_hom.id _)
  (λ g, free_group.hom_ext
    (by simp [of'_eq_of_pow, gpowers_hom, mul_assoc]))

@[simp] lemma lhs_comp_inr : (lhs r).comp inr = monoid_hom.id _ :=
by simp [lhs]

@[simp] lemma lhs_inr (g : G) : lhs r (inr g) = g := by simp [lhs]

@[simp] lemma lhs_comp_inl : (lhs r).comp inl = free_group.lift (λ g, mul_aut.conj g r) :=
by simp [lhs]

lemma lhs_inl (w : free_group G) :
  lhs r (inl w) = free_group.lift (λ g, mul_aut.conj g r) w :=
by simp [lhs]

/--  -/
def trans (p q : P G) : P G :=
⟨p.1 * q.1, q.2⟩

lemma trans_eq (p q : P G) : trans p q = p * inr p.right⁻¹ * q :=
semidirect_product.ext _ _ (by simp [trans, right_hom]) (by simp [trans, right_hom])

@[simp] lemma trans_right (p q : P G) : (p.trans q).right = q.right :=
by simp [right_hom, trans]

@[simp] lemma lhs_trans (p q : P G) : lhs r (p.trans q) = lhs r p * p.right⁻¹ * lhs r q :=
by simp [lhs, right_hom, trans_eq]

section map

/-- This is mainly used with `f` being `remove_subscript` which is not injective,
  nor is it injective on the words on which it is used. -/
def map (f : G →* H) (hf : injective f) : P G →* P H :=
semidirect_product.map (free_group.embedding ⟨f, hf⟩) f
  (λ g, free_group.hom_ext (by simp))

@[simp] lemma map_id : map (monoid_hom.id G) injective_id = monoid_hom.id (P G) :=
semidirect_product.hom_ext (free_group.hom_ext (by simp [map]))
  (monoid_hom.ext $ by simp [map])

/-- `change_r w` take a certificate of a congruence modulo `w * r * w⁻¹`
  and returns a certificate of a congruence modulo `r` -/
def change_r (w : G) : P G →* P G :=
semidirect_product.map (free_group.equiv (equiv.mul_right w)).to_monoid_hom
  (monoid_hom.id _)
  (λ g, free_group.hom_ext $ by simp [mul_assoc])

@[simp] lemma lhs_comp_change_r (r w : G) :
  (lhs r).comp (change_r w) = lhs (w * r * w⁻¹) :=
semidirect_product.hom_ext (free_group.hom_ext
  (by simp [change_r, mul_assoc, lhs_inl]))
  (by simp [monoid_hom.comp_assoc, change_r])

@[simp] lemma right_hom_comp_change_r (w : G) (x : P G) :
  right_hom.comp (change_r w) = right_hom := rfl

end map

end P

/-- `solver r T` is defined to be the type `free_group ι → option (P (free_group ι))`.
By convention, a `solver r T` will solve the word problem with respect to `r` and `T` -/
@[reducible] def solver {ι : Type} [decidable_eq ι] (r : free_group ι) (T : set ι) : Type :=
free_group ι → option (P (free_group ι))