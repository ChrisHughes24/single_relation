import .inductive_step_functor
/-!
# HNN normalization for the group_thingy tactic

This file implements the HNN normalization process and proof certificate
generation for the `group_thingy` tactic.

## Main definitions

This file contains the definition `HNN_normalize`, which is the only definition
in this file used outside of this file.

## Implementation notes

Both `HNN_normalize_core` and `reduce_mul` use an ad-hoc implementation of the
binary coproduct of `P (free_group (ι × C∞))` and `C∞`.
The representation is in reverse, i.e. the list `[(p, a), (q, b)]` represents
the word `b * q * a * p` in the coproduct. The word returned will be reduced in the
sense that the only occurence of `1` will be either `prod.fst` of the first
element of the list, or `prod.snd` of the final element.

-/

variables {ι : Type} [decidable_eq ι]

/-- `max_subscript x w`, returns the largest `k` such that
the letter `(x, k)` appears in `w`, or `none` if there is no such occurence -/
@[inline] def max_subscript (x : ι) (w : free_group (ι × C∞)) : option C∞ :=
(w.to_list.filter_map
  (λ i : Σ i : ι × C∞, C∞, if i.1.1 = x then some i.1.2 else none)).maximum

/-- `min_subscript x w`, returns the smallext `k` such that
the letter `(x, k)` appears in `w`, or `none` if there is no such occurence -/
@[inline] def min_subscript (x : ι) (w : free_group (ι × C∞)) : option C∞ :=
(w.to_list.filter_map
  (λ i : Σ i : ι × C∞, C∞, if i.1.1 = x then some i.1.2 else none)).minimum

open free_group multiplicative semidirect_product

def reduce_cons' : P (free_group (ι × C∞)) × C∞ →
  list (P (free_group (ι × C∞)) × C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| p [] := [p]
| (p, n) ((q, m)::l) :=
  if n = 1
    then (p * q, m) :: l
    else (p, n) :: (q, m) :: l

/-- `Icc_prod x a b` is the set of pairs `(i, n)` such that if
  `i = x` then `a ≤ n ≤ b` -/
def Icc_prod (x : ι) (a b : C∞) : set (ι × C∞) :=
{ p | p.1 = x → a ≤ p.2 ∧ p.2 ≤ b }

instance (x : ι) (a b : C∞) : decidable_pred (Icc_prod x a b) :=
by dunfold Icc_prod; apply_instance

/-- If `p` is a certificate that `a` and `b` are equal, then
  `remove_subscript t (conj_P t k p)`,
  will return a certificate that `t^k * remove_subscript t a * t^(-k)`
  is congruent to `t^k * remove_subscript t b * t^(-k)`  -/
def conj_P (t : ι) (k : C∞) (p : P (free_group (ι × C∞))) : P (free_group (ι × C∞)) :=
⟨mul_free (of' (t, 1) k) p.left, mul_subscript k p.right⟩

/-- `HNN_normalize_core` returns a normalized word in the `HNN` extension,  -/
meta def HNN_normalize_core'
  (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  list (Σ i : ι, C∞) →
  list (P (free_group (ι × C∞)) × C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| []     p   := p
| (i::l) [] :=
  if i.1 = t
    then HNN_normalize_core' l [(1, i.2)]
    else HNN_normalize_core' l [(inr (⟨[⟨(i.1, 1), i.2⟩], sorry⟩ : free_group (ι × C∞)), 1)]
| (i::l₁) ((p, n) :: l₂) :=
  if i.1 = t
    then if 1 ≤ i.2
      then match hs r' (Icc_prod x a (b * (of_add 1)⁻¹)) p.right with
        | none   := HNN_normalize_core' l₁ ((1, i.2) :: (p, n) :: l₂)
        | some q :=
          -- k is the maximum amount I can add to the subscripts and stay between a and b
          let k : C∞ := match max_subscript x q.right with
          | some k := min i.2 (b * k⁻¹)
          | none   := i.2
          end in
          HNN_normalize_core'
            (let m := i.2 * k⁻¹ in
              if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
            (reduce_cons' (conj_P t k (P.trans p q), n * k) l₂)
          -- HNN_normalize_core
          --   (let m := i.2 * (of_add 1)⁻¹ in
          --     if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
          --   (reduce_cons (P.change_r (of (t, 1)) (P.map
          --       (@mul_subscript ι _ (of_add 1)).to_monoid_hom sorry
          --         (P.trans p q)),
          --     n * (of_add 1)) l₂)
        end
      else match hs r' (Icc_prod x (a * of_add 1) b) p.right with
        | none   := HNN_normalize_core' l₁ ((1, i.2) :: (p, n) :: l₂)
        | some q :=
          -- k is the minimum amount I can add to the subscripts and stay between a and b
          let k : C∞ := match min_subscript x q.right with
          | some k := max i.2 (a * k⁻¹)
          | none   := i.2
          end in
          HNN_normalize_core'
            (let m := i.2 * k⁻¹ in
              if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
            (reduce_cons' (conj_P t k (P.trans p q), n * k) l₂)
          -- HNN_normalize_core
          --   (let m := i.2 * (of_add 1) in
          --     if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
          --   (reduce_cons (P.change_r (of (t, 1))⁻¹ (P.map
          --       (@mul_subscript ι _ ((of_add 1)⁻¹)).to_monoid_hom sorry
          --         (P.trans p q)),
          --     n * (of_add 1)⁻¹) l₂)
          end
    else HNN_normalize_core' l₁ ((inr (of' (i.1, 1) i.2) * p, n) :: l₂)

/-- `reduce_mul (p, n) l`, returns `l * n * p` if `l`is though
of as an elemen of the binary coproduct of `P (free_group (ι × C∞))` and `C∞`. -/
def reduce_mul : P (free_group (ι × C∞)) × C∞ →
  list (P (free_group (ι × C∞)) × C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| p [] := [p]
| (p, n) ((q, m)::l) :=
  if n = 1
    then (q * p, m) :: l
    else (p, n) :: (q, m) :: l

/-- `HNN_normalize_core` returns a normalized word in the `HNN` extension.
It is returned as a `list (P (free_group (ι × C∞)) × C∞)` which can be thought of
as an element of the binary conproduct of `P (free_group (ι × C∞))` and `C∞`.
The representation is in reverse, i.e. the list `[(p, a), (q, b)]` represents
the word `b * q * a * p` in the coproduct. The word returned will be reduced in the
sense that the only occurence of `1` will be either `prod.fst` of the first
element of the list, or `prod.snd` of the final element.

The function takes an already HNN normalized word `l₁` in the coproduct as
a `list (P (free_group (ι × C∞)) × C∞)`, and an unnormalized word `l₂`
in `free_group ι`, as a `list (Σ i : ι, C∞)`.

The function effectively returns the product `l₁ * l₂` as an HNN normalized word
in the coproduct. -/
@[inline] meta def HNN_normalize_core
  (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  list (P (free_group (ι × C∞)) × C∞) →
  list (Σ i : ι, C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| p []       := p
| [] (i::l) :=
  if i.1 = t
    then HNN_normalize_core [(1, i.2)] l
    else HNN_normalize_core [(inr (⟨[⟨(i.1, 1), i.2⟩], sorry⟩ : free_group (ι × C∞)), 1)] l
| ((p, n) :: l₁) (i::l₂) :=
  if i.1 = t
    then if 1 ≤ i.2
      then match hs r' (Icc_prod x (a * of_add 1) b) p.right with
        | none   := HNN_normalize_core ((1, i.2) :: (p, n) :: l₁) l₂
        | some q :=
          -- k is the minimum amount I can subtract from the subscripts
          -- and stay between a and b
          let k : C∞ := match min_subscript x q.right with
          | some k := max (i.2⁻¹) (a * k⁻¹)
          | none   := i.2⁻¹
          end in
          HNN_normalize_core
            (reduce_mul ((conj_P t k (P.trans p q)), n * k⁻¹) l₁)
            (let m := i.2 * k in
              if m = 1 then l₂ else ⟨t, m⟩ :: l₂)
        end
      else match hs r' (Icc_prod x a (b * (of_add 1)⁻¹)) p.right with
        | none   := HNN_normalize_core ((1, i.2) :: (p, n) :: l₁) l₂
        | some q :=
          -- k is the maximum amount I can subtract from the subscripts
          -- and stay between a and b
          let k : C∞ := match max_subscript x q.right with
          | some k := min (i.2⁻¹) (b * k⁻¹)
          | none   := i.2⁻¹
          end in
          HNN_normalize_core
            (reduce_mul ((conj_P t k (P.trans p q)), n * k⁻¹) l₁)
            (let m := i.2 * k in
              if m = 1 then l₂ else ⟨t, m⟩ :: l₂)
          end
    else HNN_normalize_core ((p * inr (of' (i.1, 1) i.2), n) :: l₁) l₂

/-- Given a word `w` in `free_group ι`, `HNN_normalize` checks whether it
can be written in the form `g * t^n`, with `g` a `t`-free word in the
HNN extension. If it cannot be written in this form `HNN_normalize` returns `none`,
if it can then `HNN_normalize` returns this pair, along with a proof. More precisely,
it returns a pair `(p, n)` where `p` is a certificate that `w * t^(-n)` is equal
to a `t`-free term.  -/
meta def HNN_normalize' (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (w : free_group ι) : option (P (free_group (ι × C∞)) × C∞) :=
match HNN_normalize_core' t x r' a b hs w.to_list.reverse [] with
| []        := some 1
| [a]       := some a
| (a::b::l) := none
end

/-- Given a word `w` in `free_group ι`, `HNN_normalize` checks whether it
can be written in the form `t^n * g`, with `g` a `t`-free word in the
HNN extension. If it cannot be written in this form `HNN_normalize` returns `none`,
if it can then `HNN_normalize` returns this pair, along with a proof. More precisely,
it returns a pair `(p, n)` where `p` is a certificate that `t^(-n) * w` is equal
to a `t`-free term.  -/
meta def HNN_normalize (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (w : free_group ι) : option (P (free_group (ι × C∞)) × C∞) :=
match HNN_normalize_core t x r' a b hs [] w.to_list with
| []        := some 1
| [a]       := some a
| (a::b::l) := none
end
