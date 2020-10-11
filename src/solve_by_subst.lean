import P
import coprod.free_group
import initial
/-!
# Solve by substitution
This file handles the special case that there is a letter with exactly
one occurence in the relation that does not occur in `T`.
-/

variables {ι : Type} [decidable_eq ι] (T : set ι) [decidable_pred T]

open multiplicative free_group semidirect_product

/-- Auxiliary definition used for `check_subst`.
  Assuming `l = check_subst T r₂`, `r₁.reverse ++ r₂`is reduced, and
  `l₂` is a list of the variables in `r₂` and not in `T`, then it will
  return `check_subst T (of_list (r₁.reverse ++ r₂))`     -/
@[inline] meta def check_subst_core : Π (r₁ r₂ : list (Σ i : ι, C∞))
  (l₁ : list (ι × bool × (free_group ι × free_group ι))) (l₂ : list ι),
  list (ι × bool × (free_group ι × free_group ι)) × list ι
| []          w₂ l₁ l₂ := (l₁, l₂)
| (⟨i,a⟩::w₁) w₂ l₁ l₂ :=
  if i ∈ T
    then check_subst_core w₁ (⟨i, a⟩::w₂) l₁ l₂
    else if i ∈ l₂
      then check_subst_core w₁ (⟨i, a⟩::w₂) (l₁.erasep (λ j, j.1 = i)) l₂
      else if a = of_add 1
        then check_subst_core w₁ (⟨i, a⟩::w₂)
          ((i, tt, of_list w₁.reverse, of_list w₂) :: l₁)
          (i :: l₂)
        else check_subst_core w₁ (⟨i, a⟩::w₂)
          ((i, ff, of_list w₁.reverse, of_list w₂) :: l₁)
          (i::l₂)

/-- `check_subst T r` returns a list containing the letters that occur exactly once in `r`,
  and do not occur in `T`.
  For each letter, there is a `bool` describing the power this letter is raised to. `tt`
  corresponds to `1`, `ff` to `-1`. It also returns two elements of the free group, `w₁` and
  `w₂` such that `r = w₁ * of i ^ ε * w₂`, where `ε = ±1` -/
@[inline] meta def check_subst (r : free_group ι) :
  list (ι × bool × free_group ι × free_group ι) :=
(check_subst_core T r.to_list.reverse [] [] []).fst

/-- `subst_proof T r` checks if there is a letter `i` that occurs exactly once in `r` and
  is not in `T`. If there is such a letter, it returns the letter `i` and a certificate
  of a congrunce `of i ≡ w` where `w` does not contain `i`. -/
@[inline] meta def subst_proof (r : free_group ι) : option (P (free_group ι) × ι) :=
match check_subst T r with
| []            := none
| (⟨i, tt, w₁, w₂⟩ :: l) :=
  some $ (⟨of (w₁⁻¹), w₁⁻¹ * w₂⁻¹⟩, i)
| (⟨i, ff, w₁, w₂⟩ :: l) :=
  some $ (⟨(of w₂)⁻¹, w₂ * w₁⟩, i)
end

/-- `solve_by_subst` attempts to solve the word problem by finding a letter with exactly
one occurence in `r` that does not occur in `T`, and substituting that letter for
a word not containing that letter. It fails when there is no such letter.  -/
@[inline] meta def solve_by_subst (r : free_group ι) : solver r T :=
λ w, do (p, i) ← subst_proof T r,
  let p' : P (free_group ι) :=
    free_group.lift'
      (λ j, if j = i
        then gpowers_hom _ p
        else inr.comp (of' j)) w in
  if mem_closure_var T p'.right
    then some p'
    else none
