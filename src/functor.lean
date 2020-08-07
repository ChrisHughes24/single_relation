import group_theory.semidirect_product for_mathlib.coprod.free_group

noncomputable theory

variables {G : Type} [group G] [decidable_eq G]
variables {H : Type} [group H] [decidable_eq H]
variables {K : Type} [group K] [decidable_eq K]

open free_group semidirect_product function

def mul_left {G : Type*} [group G] : G →* equiv.perm G :=
{ to_fun := λ g,
  { to_fun := λ h, g * h,
    inv_fun := λ h, g⁻¹ * h,
    left_inv := λ _, by simp [mul_assoc],
    right_inv := λ _, by simp [mul_assoc] },
  map_one' := by ext; simp,
  map_mul' := λ _ _, by ext; simp [mul_assoc] }

@[simp] lemma coe_fn_mul_left {G : Type*} [group G] (g : G) : (⇑(_root_.mul_left g) : G → G) = (*) g := rfl
@[simp] lemma coe_fn_mul_left_symm {G : Type*} [group G] (g : G) : (⇑(_root_.mul_left g).symm : G → G) = (*) g⁻¹ := rfl

def mul_free : G →* mul_aut (free_group G) :=
{ to_fun := λ g, free_group.equiv (_root_.mul_left g),
  map_mul' := by simp [mul_aut.mul_def, equiv.perm.mul_def],
  map_one' := by simp [mul_aut.one_def, equiv.perm.one_def] }

@[simp] lemma mul_free_of' (g : G) (h : G) (n : C∞) :
  mul_free g (of' h n) = of' (g * h) n :=
by simp [mul_free]

@[simp] lemma mul_free_of (g : G) (h : G) : mul_free g (of h) = of (g * h) :=
by simp [mul_free, of_eq_of']

@[simp] lemma mul_free_inv_of (g : G) (h : G) : (mul_free g)⁻¹ (of h) = of (g⁻¹ * h) :=
by rw [← monoid_hom.map_inv, mul_free_of]

variable (G)
@[reducible] def P : Type* := free_group G ⋊[mul_free] G

variable {G}
namespace P

variables {r rG : G} {rH : H} {rK : K}

instance : group (P G) := semidirect_product.group

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

@[simp] lemma lhs_inl (w : free_group G) :
  lhs r (inl w) = free_group.lift (λ g, mul_aut.conj g r) w :=
by simp [lhs]

def trans (x y : P G) : P G :=
⟨x.1 * y.1, y.2⟩

lemma trans_eq (x y : P G) : trans x y = x * inr x.right⁻¹ * y :=
semidirect_product.ext _ _ (by simp [trans, right_hom]) (by simp [trans, right_hom])

@[simp] lemma trans_right (x y : P G) : (x.trans y).right = y.right :=
by simp [right_hom, trans]

@[simp] lemma lhs_trans (x y : P G) : lhs r (x.trans y) = lhs r x * x.right⁻¹ * lhs r y :=
by simp [lhs, right_hom, trans_eq]

section map

def map (f : G →* H) (hf : injective f) : P G →* P H :=
semidirect_product.map (free_group.embedding ⟨f, hf⟩) f
  (λ g, free_group.hom_ext (by simp))

@[simp] lemma map_id : map (monoid_hom.id G) injective_id = monoid_hom.id (P G) :=
semidirect_product.hom_ext (free_group.hom_ext (by simp [map]))
  (monoid_hom.ext $ by simp [map])

def change_r (r w : G) : P G →* P G :=
semidirect_product.map (free_group.equiv (equiv.mul_right w⁻¹)).to_monoid_hom
  (monoid_hom.id _)
  (λ g, free_group.hom_ext $ by simp [mul_assoc])

@[simp] lemma lhs_comp_change_r (r w : G) :
  (lhs (w * r * w⁻¹)).comp (change_r r w) = lhs r :=
semidirect_product.hom_ext (free_group.hom_ext
  (by simp [change_r, mul_assoc]))
  (by simp [monoid_hom.comp_assoc, change_r])

@[simp] lemma right_hom_comp_change_r (r w : G) (x : P G) :
  right_hom.comp (change_r r w) = right_hom := rfl

end map

end P
