import coprod.free_group
import group_theory.semidirect_product
/-!
# Initial file for `group_thingy` tactic

This file contains notation `C∞` for `multiplicative ℤ`, and `repr` instances
for `free_group` and `semidirect_product`
-/
notation `C∞` := multiplicative ℤ

variables {ι : Type} [decidable_eq ι]

instance : has_repr C∞ := int.has_repr

instance [has_repr ι] : has_repr (free_group ι) :=
⟨λ x, repr x.to_list⟩

instance {G H : Type*} [group G] [group H] [has_repr G] [has_repr H] (φ) :
  has_repr (G ⋊[φ] H) := ⟨λ g, "⟨" ++ repr g.1 ++ ", " ++ repr g.2 ++ "⟩" ⟩

/-- `mem_closure_var T w` is true when `w` contains only letters from `T`.  -/
def mem_closure_var (T : set ι) [decidable_pred T] (w : free_group ι) : bool :=
w.to_list.all (λ i, i.1 ∈ T)

/-- `of_list` is an unsafe function turning a ` list (Σ i : ι, C∞)` into
  an element of the `free_group`, ignoring the proof that the list is reduced. -/
meta def of_list {ι : Type} (l : list (Σ i : ι, C∞)) : free_group ι := ⟨l, undefined⟩
