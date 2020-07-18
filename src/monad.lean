import group_theory.semidirect_product for_mathlib.coproduct

namespace whatever

noncomputable theory

variables {G : Type*} [group G] [decidable_eq G]
variables {H : Type*} [group H] [decidable_eq H]
variables {K : Type*} [group K] [decidable_eq K]

open free_group semidirect_product

def mul_free : G →* mul_aut (free_group G) :=
{ to_fun := λ g, free_group.equiv (mul_left g),
  map_mul' := by simp [mul_aut.mul_def, equiv.perm.mul_def],
  map_one' := by simp [mul_aut.one_def, equiv.perm.one_def] }

@[simp] lemma mul_free_of' (g : G) (h : G) (n : C∞):
  mul_free g (of' h n) = of' (g * h) n :=
by simp [mul_free]

variable G
def P : Type* := free_group G ⋊[mul_free] G

-- map sends g ∈ G to g * r * g⁻¹
-- image of this map is the normal closure of {r}

variable {G}
instance : group (P G) := by dunfold P; apply_instance

def pure : G →* P G := inr

def unpure (r : G) : P G →* G :=
semidirect_product.lift (free_group.lift (λ g, mul_aut.conj g r))
  (monoid_hom.id _)
  (λ g, free_group.hom_ext
    (by simp [free_group.lift, of_eq_of', ii, multiplicative.to_add, gpowers_hom,
      mul_assoc]))

def bind' (rG : G) (rH : H) (f : G →* P H) : P G →* P H :=
monoid_hom.comp f (unpure rG)

def bind (rG : G) (f : G → P H) : P G → P H :=
λ x, f (unpure rG x)

def map (rG : G) (f : G → H) (g : P G) : P H :=
bind rG (pure ∘ f) g

lemma map_id (rG : G) (g : P G) : map rG id g = g :=
by cases g; simp [map, bind, pure, unpure]

lemma bind_assoc (rG : G) (rH : H) (f : G → P H) (g : H → P K) (x : P G) :
  bind rH g (bind rG f x) = bind rG (λ y, bind rH g (f y)) x :=
begin
  refine semidirect_product.ext _ _ _ _;
  simp [bind]
end

lemma bind_pure (rG: G) (f : G → P H) (g : G) : bind rG f (pure g) = f g :=
begin
  refine semidirect_product.ext _ _ _ _;
  simp [bind, unpure, pure]
end

lemma pure_bind (rG: G) (f : G → P H) (g : P G) : bind rG pure g = g :=
begin
  refine semidirect_product.ext _ _ _ _;
  cases g;
  simp [bind, unpure, pure],
end


end whatever