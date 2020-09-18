import .inductive_step_functor
/-!
# HNN normalization for the group_thingy tactic

This file contains the

-/

variables {ι : Type} [decidable_eq ι]

def max_subscript (x : ι) (w : free_group (ι × C∞)) : option C∞ :=
(w.to_list.filter_map
  (λ i : Σ i : ι × C∞, C∞, if i.1.1 = x then some i.1.2 else none)).maximum

def min_subscript (x : ι) (w : free_group (ι × C∞)) : option C∞ :=
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

def Icc_prod (x : ι) (a b : C∞) : set (ι × C∞) :=
{ p | p.1 = x → a ≤ p.2 ∧ p.2 ≤ b }

instance (x : ι) (a b : C∞) : decidable_pred (Icc_prod x a b) :=
by dunfold Icc_prod; apply_instance

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

def reduce_cons : P (free_group (ι × C∞)) × C∞ →
  list (P (free_group (ι × C∞)) × C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| p [] := [p]
| (p, n) ((q, m)::l) :=
  if n = 1
    then (q * p, m) :: l
    else (p, n) :: (q, m) :: l

/-- `HNN_normalize_core` returns a normalized word in the `HNN` extension,  -/
meta def HNN_normalize_core
  (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  list (Σ i : ι, C∞) →
  list (P (free_group (ι × C∞)) × C∞) →
  list (P (free_group (ι × C∞)) × C∞)
| []     p   := p
| (i::l) [] :=
  if i.1 = t
    then HNN_normalize_core l [(1, i.2)]
    else HNN_normalize_core l [(inr (⟨[⟨(i.1, 1), i.2⟩], sorry⟩ : free_group (ι × C∞)), 1)]
| (i::l₁) ((p, n) :: l₂) :=
  if i.1 = t
    then if 1 ≤ i.2
      then match hs r' (Icc_prod x (a * of_add 1) b) p.right with
        | none   := HNN_normalize_core l₁ ((1, i.2) :: (p, n) :: l₂)
        | some q :=
          let k : C∞ := match min_subscript x q.right with
          | some k := max (i.2⁻¹) (a * k⁻¹)
          | none   := i.2⁻¹
          end in
          HNN_normalize_core
            (let m := i.2 * k in
              if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
            (reduce_cons ((conj_P t k (P.trans p q)), n * k⁻¹) l₂)
        end
      else match hs r' (Icc_prod x a (b * (of_add 1)⁻¹)) p.right with
        | none   := HNN_normalize_core l₁ ((1, i.2) :: (p, n) :: l₂)
        | some q :=
          -- k is the minimum amount I can add to the subscripts and stay between a and b
          let k : C∞ := match max_subscript x q.right with
          | some k := min (i.2⁻¹) (b * k⁻¹)
          | none   := i.2⁻¹
          end in
          HNN_normalize_core
            (let m := i.2 * k in
              if m = 1 then l₁ else ⟨t, m⟩ :: l₁)
            (reduce_cons ((conj_P t k (P.trans p q)), n * k⁻¹) l₂)
          end
    else HNN_normalize_core l₁ ((p * inr (of' (i.1, 1) i.2), n) :: l₂)

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

meta def HNN_normalize (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (w : free_group ι) : option (P (free_group (ι × C∞)) × C∞) :=
match HNN_normalize_core t x r' a b hs w.to_list [] with
| []        := some 1
| [a]       := some a
| (a::b::l) := none
end

