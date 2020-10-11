import P
import initial
/-! This file handles the case that all letters in `r` are in `T` -/

variables {ι : Type} [decidable_eq ι] (T : set ι) [decidable_pred T]
  (r : free_group ι) (vars_r : list ι) (hs : solver r ∅)

open semidirect_product free_group

/-- `no_letters_reduce_mul (p, w) l`, returns `p * w * l` if `l`is thought
of as an element of the binary coproduct of `P (free_group ι)` and `free_group ι`. -/
def no_letters_reduce_mul : P (free_group ι) × free_group ι →
  list (P (free_group ι) × free_group ι) →
  list (P (free_group ι) × free_group ι)
| p [] := [p]
| (p, w₁) ((q, w₂)::l) :=
  if w₁ = 1
    then (q * p, w₂) :: l
    else (p, w₁) :: (q, w₂) :: l


meta def no_letters_core : Π (l : list (Σ i : ι, C∞))
  (l₂ : list (P (free_group ι) × free_group ι)),
  list (P (free_group ι) × free_group ι)
| []        l₂ := l₂
| (i::l)   [] :=
  if i.1 ∈ T
    then no_letters_core l [(inr (of_list [i]), 1)]
    else no_letters_core l [(1, of_list [i])]
| (i::l₁) ((p, w) :: l₂) :=
  if i.1 ∈ T
    then no_letters_core l₁ ((p * inr (of_list [i]), w) :: l₂)
    else match hs p.right with
      | none     := no_letters_core l₁ ((1, of_list [i]) :: (p, w) :: l₂)
      | (some q) := no_letters_core l₁
          (no_letters_reduce_mul
            (⟨mul_free (of_list [⟨i.1, i.2⁻¹⟩]) (p.1 * q.1), 1⟩, w * of_list [i]) l₂)
      end

meta def no_letters : solver r T :=
λ w, let p : P (free_group ι) :=
  (no_letters_core T r hs w.to_list []).foldl
    (λ x y, inr y.2 * y.1 * x) 1 in
if mem_closure_var T p.right
  then some p
  else none
