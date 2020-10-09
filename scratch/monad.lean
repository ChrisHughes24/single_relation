import group_theory.semidirect_product for_mathlib.coproduct

namespace whatever

noncomputable theory

variables {G : Type} [group G] [decidable_eq G]
variables {H : Type} [group H] [decidable_eq H]
variables {K : Type} [group K] [decidable_eq K]

open free_group semidirect_product

def mul_free : G →* mul_aut (free_group G) :=
{ to_fun := λ g, free_group.equiv (mul_left g),
  map_mul' := by simp [mul_aut.mul_def, equiv.perm.mul_def],
  map_one' := by simp [mul_aut.one_def, equiv.perm.one_def] }

@[simp] lemma mul_free_of' (g : G) (h : G) (n : C∞) :
  mul_free g (of' h n) = of' (g * h) n :=
by simp [mul_free]

@[simp] lemma mul_free_of (g : G) (h : G) : mul_free g (of h) = of (g * h) :=
by simp [mul_free, of_eq_of']

variable G
def P : Type := free_group G ⋊[mul_free] G

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

def bind'' (f : G → P H) : P G → P H :=
λ x, ⟨free_group.lift (λ g, of (f g).right) x.left * (f x.right).left, (f x.right).right⟩
-- λ x, (inl.comp (free_group.lift (λ g, mul_aut.conj (f g).left (of (f g).right)))) x.left *
--   f x.right

def map'' (f : G → H) (g : P G) : P H :=
bind'' (pure ∘ f) g

def join'' : P (P G) → P G :=
bind'' id

-- example (x : P (P G)): join'' x = ⟨x.1 * x.2.1, _⟩

-- example (rG : G) (rH : H) (f : G →* H) (h : f rG = rH) (g : P G) :
--   unpure rH (map'' f g) = f (unpure rG g) :=
-- begin
--   cases g,
--   subst h,
--   simp [unpure, map'', bind'', pure, mul_assoc],
--   refine free_group.rec_on g_left _ _,
--   { simp },
--   { intros,
--     simp * }
-- end

def bind''' (f : G →* P H) : P G →* P H :=
semidirect_product.lift
  (inl.comp (free_group.lift (λ g, mul_aut.conj (f g).left (of (f g).right))))
  f
(λ g, free_group.hom_ext begin
  assume i,
  refine semidirect_product.ext _ _ _ _,
  { simp,
    cases f g;
    simp [mul_aut.inv_def, mul_assoc, mul_equiv.map_mul, mul_equiv.map_inv] },
  { simp, }
end)


lemma bind_assoc (rG : G) (rH : H) (f : G → P H) (g : H → P K) (x : P G) :
  bind rH g (bind rG f x) = bind rG (λ y, bind rH g (f y)) x :=
begin
  refine semidirect_product.ext _ _ _ _;
  simp [bind]
end

lemma bind_pure (rG : G) (f : G → P H) (g : G) : bind rG f (pure g) = f g :=
begin
  refine semidirect_product.ext _ _ _ _;
  simp [bind, unpure, pure]
end

-- lemma pure_bind (rG : G) (g : P G) : bind rG pure g = g :=
-- begin
--   refine semidirect_product.ext _ _ _ _;
--   cases g;
--   simp [bind, unpure, pure],
-- end

lemma bind''_assoc (rG : G) (rH : H) (f : G → P H) (g : H → P K) (x : P G) :
  bind''  g (bind''  f x) = bind''  (λ y, bind'' g (f y)) x :=
begin
  refine semidirect_product.ext _ _ _ _,
  { cases x with xl xr,
    simp [bind'', mul_assoc],
    simp only [← monoid_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    refine free_group.hom_ext _,
    simp },
  { simp [bind'', mul_assoc] }
end

lemma bind''_pure (rG: G) (f : G → P H) (g : G) : bind'' f (pure g) = f g :=
begin
  refine semidirect_product.ext _ _ _ _;
  simp [bind'', unpure, pure],
end

lemma pure_bind'' (rG: G) (g : P G) : bind'' pure g = g :=
begin
  refine semidirect_product.ext _ _ _ _;
  cases g;
  simp [bind'', unpure, pure],
  conv_rhs { rw ← monoid_hom.id_apply g_left },
  refine congr_fun _ _,
  refine congr_arg _ _,
  refine free_group.hom_ext _,
  simp [free_group.lift, of_eq_of', gpowers_hom, ii, multiplicative.to_add],
end

local attribute [instance] classical.dec


def M (α : Type) : Type := free_group α × α

instance : monad M :=
{ bind := λ α β m f, show M β,
    from ⟨free_group.lift (λ g, (of (f g).2)) m.1 * (f m.2).1, (f m.2).2⟩,
  pure := λ α a, (1, a) }

instance : is_lawful_functor M :=
{ id_map := λ α x, begin
    cases x,
    simp [functor.map],
    conv_rhs { rw ← monoid_hom.id_apply x_fst },
    refine congr_fun (congr_arg _ _) _,
    refine free_group.hom_ext _,
    simp
  end,
  comp_map := λ α β γ g h x, begin
    cases x,
    simp [functor.map],
    simp only [← monoid_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    refine free_group.hom_ext _,
    simp
  end }

instance : is_lawful_monad M :=
{ pure_bind := λ α β x f, by simp [has_bind.bind, has_pure.pure],
  bind_assoc := λ α β γ x f g,
    begin
      cases x,
      simp [has_bind.bind, has_pure.pure, mul_assoc],
      simp only [← monoid_hom.comp_apply],
      refine congr_fun (congr_arg _ _) _,
      refine free_group.hom_ext _,
      simp
    end }

def mul (x y : M G) : M G :=
x >>= (λ x', (λ y', x' * y') <$> y)
#print functor.map
lemma mul_def (x y : M G) : mul x y =
  (x.1 * mul_free x.2 y.1, x.2 * y.2) :=
begin
  simp [mul, has_bind.bind, return, has_pure.pure, functor.map],
  cases y,
  refine free_group.rec_on y_fst _ _,
  simp [mul_equiv.map_mul], admit,
  simp [mul_equiv.map_mul],

end


end whatever