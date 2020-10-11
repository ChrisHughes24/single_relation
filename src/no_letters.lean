import P
import initial
/-!
# No letters
This file handles the case that all letters in `r` are in `T`

## Implementation Notes
Every function in this file uses an ad-hoc implementation of the
binary coproduct of `P (free_group T)` and `free_group Tᶜ`. It is implemented as
a `list (P (free_group ι) × free_group ι)`.
The representation is in reverse, i.e. the list `[(p, a), (q, b)]` represents
the word `b * q * a * p` in the coproduct. The word returned will be reduced in the
sense that the only occurence of `1` will be either `prod.fst` of the first
element of the list, or `prod.snd` of the final element.

-/

variables {ι : Type} [decidable_eq ι] (T : set ι) [decidable_pred T]
  (r : free_group ι) (hs : solver r ∅)

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

/-- Auxiliary definition used to define `no_letters`. `no_letters_core r T l₁ l₂` effectively
  returns a normalization `l₁ * l₂` when `l₁` is regarded as an element of `free_group ι`
  and `l₂` as the coproduct of `P (free_group T)` and `free_group Tᶜ`. Normalized means that
  every letter in `P (free_group T)` that is equal to `1` in the quotient by `r` is rewritten
  to be `1`, and that if the `right` of any element of `P (free_group T)` is `1`, then this is
  the first element in the list. -/
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

/-- `no_letters` solves the word problem when every letter in `r` is in `T`. -/
meta def no_letters : solver r T :=
λ w, let p : P (free_group ι) :=
  (no_letters_core T r hs w.to_list []).foldl
    (λ x y, inr y.2 * y.1 * x) 1 in
if mem_closure_var T p.right
  then some p
  else none
