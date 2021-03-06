import coprod.free_group
import initial
/-!
# Cyclically reducing words
This file contains three functions `cyclically_reduce`, `cyclically_conjugate` and
`min_max_subscript`
-/
variables {ι : Type} [decidable_eq ι]

open free_group mul_aut multiplicative

/-- Given a word `r` returns a pair `(g, r')` such that `r'` is cyclically reduced
  and `g * r * g⁻¹ = r'`. Cyclically reduced means that if it contains more than
  one distinct letter, then it starts and finishes with a different letter. -/
@[inline] meta def cyclically_reduce : free_group ι → free_group ι × free_group ι
| ⟨[], _⟩      := (1, 1)
| ⟨[i], h⟩     := (1, ⟨[i], h⟩)
| ⟨i::j::l, h⟩ :=
  let k := (j :: l : list _).last (list.cons_ne_nil _ _) in
  if i.1 = k.1
  then
    let z := k.2 * i.2 in
    if z = 1
    then
      let init : free_group ι := of_list (j :: l : list _).init in
      let w' := cyclically_reduce init in
      (w'.1 * of' k.1 k.2, w'.2)
    else
      (of' k.1 k.2, of_list (⟨k.1, z⟩ ::  (j :: l : list _).init))
  else (1, ⟨i::j::l, h⟩)

/-- Given a word `r` and a letter `x` returns a pair `(g, r')` such that `r'` begins with `x`
  and `g * r * g⁻¹ = r'`  -/
@[inline] meta def cyclically_conjugate (x : ι) (w : free_group ι) : free_group ι × free_group ι :=
let n : ℕ := w.to_list.find_index (λ i, i.1 = x) in
⟨(of_list (w.to_list.take n))⁻¹, of_list (w.to_list.rotate n)⟩

/-- `min_max_subscript x r` returns the minimum and maximum `n` such that
  `(x, n)` is a letter in `r`, assuming that `(x, 1)` is a letter in `r`.  -/
@[inline] def min_max_subscript (x : ι) (r : free_group (ι × C∞)) : C∞ × C∞ :=
r.to_list.foldl
  (λ minmax i,
    if i.1.1 = x
      then (min i.1.2 minmax.1, max i.1.2 minmax.2)
      else minmax)
  1
