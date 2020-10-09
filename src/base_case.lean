import P
import coprod.free_group_subgroup
import initial
/-!
# The base case of the `group_thingy` tactic

## Main definitions
The only definition used outside of this file is `base_case_solver`.
`base_case_solver T r₁ r₂` solves the word problem for the relation `of' r₁ r₂`, returning
a normalized word in `T` when possible, and `none` otherwise
-/
variables {ι : Type} [decidable_eq ι]

open multiplicative free_group P semidirect_product

/-- `base_case_core` takes a word `l₁` in the free_group as a `list (Σ i : ι, C∞)`
and a normalized word with proof `p` as a `P (free_group ι)`.
It returns a normalized version `reverse l₁ * p`, reduced modulo `of' r₁ r₂`  -/
@[inline] def base_case_core (r₁ : ι) (r₂ : C∞) : list (Σ i : ι, C∞) →
  P (free_group ι) → P (free_group ι)
| []     p := p
| (i::l₁)  ⟨p, ⟨[], _⟩⟩ :=
  if i.1 = r₁
    then if to_add r₂ ∣ i.2
      then let q := to_add i.2 / to_add r₂ in
        base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, 1⟩)
      else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, 1⟩)
    else base_case_core l₁ (inr (of' i.1 i.2) * inl p)
| (i::l₁) ⟨p, ⟨j::l₂, _⟩⟩ :=
  if i.1 = r₁
    then if j.1 = r₁
      then
        let x := to_add i.2 + to_add j.2 in
        if to_add r₂ ∣ x
        then base_case_core l₁ (inl (of' (1 : free_group ι) (of_add (to_add x / to_add r₂))) *
          inr (of' j.1 j.2⁻¹) * ⟨p, ⟨j::l₂, sorry⟩⟩)
        else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
      else if to_add r₂ ∣ i.2
        then let q := to_add i.2 / to_add r₂ in
          base_case_core l₁ (inl (of' (1 : free_group ι) q) * ⟨p, ⟨j::l₂, sorry⟩⟩)
        else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)
    else base_case_core l₁ (inr (of' i.1 i.2) * ⟨p, ⟨j::l₂, sorry⟩⟩)

/-- `base_case` reduces a word `w` in the `free_group ι` modulo `of' r₁ r₂` -/
@[inline] def base_case (r₁ : ι) (r₂ : C∞) (w : free_group ι) : P (free_group ι) :=
base_case_core r₁ r₂ w.to_list.reverse 1

/-- `base_case_solver T r₁ r₂` solves the word problem for the relation `of' r₁ r₂`, returning
a normalized word in `T` when possible, and `none` otherwise -/
@[inline] def base_case_solver (T : set ι) [decidable_pred T] (r₁ : ι) (r₂ : C∞) :
  solver (of' r₁ r₂) T :=
λ w,
let p := base_case r₁ r₂ w in
if p.right ∈ closure_var T
  then some p
  else none
