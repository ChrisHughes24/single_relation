import group_theory.semidirect_product for_mathlib.coproduct

noncomputable theory

variables {G : Type} [group G] [decidable_eq G]
variables {H : Type} [group H] [decidable_eq H]
variables {K : Type} [group K] [decidable_eq K]

open free_group semidirect_product function

def mul_free : G →* mul_aut (free_group G) :=
{ to_fun := λ g, free_group.equiv (mul_left g),
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
    (by simp [free_group.lift, of_eq_of', ii, multiplicative.to_add, gpowers_hom,
      mul_assoc]))

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

def map_aux (f : G →* H) (hf : injective f) : P G → P H :=
λ x, ⟨free_group.embedding ⟨f, hf⟩ x.1, f x.2⟩

def map (f : G →* H) (hf : injective f) : P G →* P H :=
{ to_fun := map_aux f hf,
  map_mul' := λ ⟨pr₁, rh₁⟩ ⟨pr₂, rh₂⟩, begin
      refine semidirect_product.ext _ _ _ _,
      { simp [map_aux],
        simp only [← monoid_hom.comp_apply, ← mul_equiv.to_monoid_hom_apply],
        refine congr_fun (congr_arg _ _) _,
        refine free_group.hom_ext _,
        simp [of_eq_of'] },
      { simp [map_aux] }
    end,
  map_one' := by simp [map_aux] }

@[simp] lemma map_id : map (monoid_hom.id G) injective_id = monoid_hom.id (P G) :=
semidirect_product.hom_ext (free_group.hom_ext (by simp [map, map_aux, of_eq_of']))
  (monoid_hom.ext $ by simp [map, map_aux])

def change_r (r w : G) (x : P G) : P G :=
⟨free_group.equiv (equiv.mul_right w⁻¹) x.1, x.2⟩

@[simp] lemma lhs_change_r (r w : G) (x : P G) :
  lhs (w * r * w⁻¹) (change_r r w x) = lhs r x :=
begin
  rw [lhs, lhs, change_r],
  cases x,
  simp,
  simp only [← monoid_hom.comp_apply, ← mul_equiv.to_monoid_hom_apply],
  refine congr_fun (congr_arg _ _) _,
  refine free_group.hom_ext _,
  simp [mul_assoc, of_eq_of', free_group.lift]
end

@[simp] lemma right_hom_change_r (r w : G) (x : P G) : right_hom (change_r r w x) = right_hom x := rfl

end map

end P
