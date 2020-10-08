import for_mathlib.coprod.free_group group_theory.semidirect_product
/-!
# Initial file for `group_thingy` tactic

This file contains notation `C∞` for `multiplicative ℤ`, and `repr` instances
for `free_group` and `semidirect_product`
-/
notation `C∞` := multiplicative ℤ

variables {ι : Type}

instance : has_repr C∞ := int.has_repr

instance [has_repr ι] [decidable_eq ι] : has_repr (free_group ι) :=
⟨λ x, repr x.to_list⟩

instance {G H : Type*} [group G] [group H] [has_repr G] [has_repr H] (φ) :
  has_repr (G ⋊[φ] H) := ⟨λ g, "⟨" ++ repr g.1 ++ ", " ++ repr g.2 ++ "⟩" ⟩

/-- `of_list` is an unsafe function turning a ` list (Σ i : ι, C∞)` into
  an element of the `free_group`, ignoring the proof that the list is reduced. -/
meta def of_list (l : list (Σ i : ι, C∞)) : free_group ι := ⟨l, undefined⟩
