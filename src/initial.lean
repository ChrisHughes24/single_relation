import for_mathlib.coprod.free_group group_theory.semidirect_product

notation `C∞` := multiplicative ℤ

variables {ι : Type}

instance : has_repr C∞ := int.has_repr

instance [has_repr ι] [decidable_eq ι] : has_repr (free_group ι) :=
⟨λ x, repr x.to_list⟩

instance {G H : Type*} [group G] [group H] [has_repr G] [has_repr H] (φ) :
  has_repr (G ⋊[φ] H) := ⟨λ g, "⟨" ++ repr g.1 ++ ", " ++ repr g.2 ++ "⟩" ⟩
