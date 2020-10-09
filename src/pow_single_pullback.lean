import P
import initial
/-!
# Pow single pullback

The main definition in this file is `pow_single_pullback`

`pow_single_pullback t n p` has the property that for any `r`
`lhs (pow_single t n r) p = pow_single t n a` and
`right p = pow_single t n b` then
`lhs r (pow_single_pullback t n p) = a` and `right (pow_single_pullback t n p) = b`

``pow_single t n` is the hom `free_group ι` to itself mapping
  `of t` to `of t ^ n` and every other letter to itself.
-/
variables {ι : Type} [decidable_eq ι]
open list multiplicative free_group

/- `pow_single` is not actually used anywhere, but it is useful to leave it defined
  as it is referred to in documentation of other functions -/
/-- `pow_single t n` is the hom `free_group ι` to itself mapping
  `of t` to `of t ^ n` and every other letter to itself. -/
def pow_single (t : ι) (n : C∞) : free_group ι →* free_group ι :=
free_group.lift (λ i, if t = i then free_group.of' i n else free_group.of i)

/-- Auxiliary definition used for `pow_single_pullback`. -/
@[inline] def pow_single_proof_pullback_core (t : ι) (n : C∞) :
  Π (l : list (Σ i : ι, C∞)), free_group ι × C∞ → free_group ι × C∞
| []     w := w
| (i::l) w :=
if t = i.1
  then if n.to_add ∣ to_add i.2 + to_add w.2
    then pow_single_proof_pullback_core l
      (w.1 * of' t (of_add ((to_add i.2 + to_add w.2) / n.to_add)), 1)
    else pow_single_proof_pullback_core l (w.1, i.2 * w.2)
  else pow_single_proof_pullback_core l (w.1 * of' i.1 i.2, w.2)

/-- `pow_single_proof_pullback` is used to define `pow_single_pullback`. -/
@[inline] def pow_single_proof_pullback (t : ι) (n : C∞) (w : free_group ι) :
  free_group ι :=
(pow_single_proof_pullback_core t n w.to_list 1).1

/-- Auxiliary definition used to deifne `powsingle_inverse` -/
@[inline] meta def pow_single_inverse_aux (t : ι) (n : C∞) :
  list (Σ i : ι, C∞) → option (free_group ι)
| []    := some (of_list [])
| (i::l)  :=
do ⟨l', _⟩ ← pow_single_inverse_aux l,
if i.1 = t
  then if to_add n ∣ i.2
    then return (of_list $ ⟨i.1, of_add $ to_add i.2 / to_add n⟩ :: l')
    else none
  else of_list $ i :: l'

/-- `pow_single_inverse t n` is the partial inverse to `pow_single t n` -/
@[inline] meta def pow_single_inverse (t : ι) (n : C∞) (w : free_group ι) :
  option (free_group ι) :=
pow_single_inverse_aux t n w.to_list

/-- `pow_single_pullback t n p` has the property that for any `r`
  `lhs (pow_single t n r) p = pow_single t n a` and
  `right p = pow_single t n b` then
  `lhs r (pow_single_pullback t n p) = a` and `right (pow_single_pullback t n p) = b` -/
@[inline] meta def pow_single_pullback (t : ι) (n : C∞) (p : P (free_group ι)) :
  option (P (free_group ι)) :=
(pow_single_inverse t n p.2).map
  (λ w, ⟨map (pow_single_proof_pullback t n) p.left, w⟩)
