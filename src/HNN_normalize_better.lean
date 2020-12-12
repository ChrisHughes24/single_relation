import initial
import P
import data.list.min_max
/-!
# HNN normalization for the group_thingy tactic

This file implements the HNN normalization process and proof certificate
generation for the `group_thingy` tactic.

## Main definitions

This file contains the definition `HNN_normalize`, which is the only definition
in this file used outside of this file.

## Implementation notes

Both `HNN_normalize_core` and `reduce_mul` use an ad-hoc implementation of the
binary coproduct of `P (free_group (ι × C∞))` and `C∞` as a `list (P (free_group (ι × C∞)) × C∞)`.
The representation is in reverse, i.e. the list `[(p, a), (q, b)]` represents
the word `b * q * a * p` in the coproduct. The word returned will be reduced in the
sense that the only occurence of `1` will be either `prod.fst` of the first
element of the list, or `prod.snd` of the final element.
-/

variables {ι : Type} [decidable_eq ι] (r : free_group ι) (T : set ι) [decidable_pred T]

open free_group P semidirect_product multiplicative

/-- `mul_subscript` is the action of `C∞` on `free_group (ι × C∞)`.
  `mul_subscript n (of (i, m)) = of (i, n * m)` -/
def mul_subscript : C∞ →* free_group (ι × C∞) ≃* free_group (ι × C∞) :=
{ to_fun := λ n, free_group.equiv (equiv.prod_congr (equiv.refl _) (equiv.mul_left n)),
  map_one' := mul_equiv.to_monoid_hom_injective (free_group.hom_ext (by simp)),
  map_mul' := λ _ _, mul_equiv.to_monoid_hom_injective (free_group.hom_ext (by simp [mul_assoc])) }

/-- `remove_subscript t (of (i, n)) = (of t)^n * of i * (of t)^(-n)` -/
def remove_subscript (t : ι) : free_group (ι × C∞) →* free_group ι :=
free_group.lift' (λ g, (mul_aut.conj (of' t g.2)).to_monoid_hom.comp (of' g.1))

/-- `add_subscript t` is a one sided inverse to `semidirect_product.inl ∘ remove_subscript t` -/
def add_subscript (t : ι) : free_group ι →* free_group (ι × C∞) ⋊[mul_subscript] C∞ :=
free_group.lift' (λ j,
  if t = j
  then semidirect_product.inr
  else semidirect_product.inl.comp (of' (j, 1)))

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

/-- If `p` is a certificate that `a` and `b` are equal, then
  `remove_subscript t (conj_P t k p)`,
  will return a certificate that `t^k * remove_subscript t a * t^(-k)`
  is congruent to `t^k * remove_subscript t b * t^(-k)`  -/
def conj_P (t : ι) (k : C∞) (p : P (free_group (ι × C∞))) : P (free_group (ι × C∞)) :=
⟨mul_free (of' (t, 1) k) p.left, mul_subscript k p.right⟩

-- /-- `reduce_mul (p, n) l`, returns `l * n * p` if `l`is thought
-- of as an element of the binary coproduct of `P (free_group (ι × C∞))` and `C∞`. -/
-- def reduce_mul : P (free_group (ι × C∞)) × C∞ →
--   list (P (free_group (ι × C∞)) × C∞) →
--   list (P (free_group (ι × C∞)) × C∞)
-- | p [] := [p]
-- | (p, n) ((q, m)::l) :=
--   if n = 1
--     then (q * p, m) :: l
--     else (p, n) :: (q, m) :: l

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
-- @[inline] meta def HNN_normalize_core
--   (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
--   (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
--   list (P (free_group (ι × C∞)) × C∞) →
--   list (Σ i : ι, C∞) →
--   list (P (free_group (ι × C∞)) × C∞)
-- | p []       := p
-- | [] (i::l) :=
--   if i.1 = t
--     then HNN_normalize_core [(1, i.2)] l
--     else HNN_normalize_core [(inr (of_list [⟨(i.1, 1), i.2⟩]), 1)] l
-- | ((p, n) :: l₁) (i::l₂) :=
--   if i.1 = t
--     then if 1 ≤ i.2
--       then match hs r' {s | s ≠ (x, a)} p.right with
--         | none   := HNN_normalize_core ((1, i.2) :: (p, n) :: l₁) l₂
--         | some q :=
--           -- k is the minimum amount I can subtract from the subscripts
--           -- and stay between a and b
--           let k : C∞ := match min_subscript x q.right with
--           | some m := if n < 1 then max (max (i.2⁻¹) (a * m⁻¹)) n else max (i.2⁻¹) (a * m⁻¹)
--           | none   := if n < 1 then max i.2⁻¹ n else i.2⁻¹
--           end in
--           HNN_normalize_core
--             (reduce_mul ((conj_P t k (P.trans p q)), n * k⁻¹) l₁) --BUG when |k| > |n|
--             (let m := i.2 * k in
--               if m = 1 then l₂ else ⟨t, m⟩ :: l₂)
--         end
--       else match hs r' {s | s ≠ (x, b)} p.right with
--         | none   := HNN_normalize_core ((1, i.2) :: (p, n) :: l₁) l₂
--         | some q :=
--           -- k is the maximum amount I can subtract from the subscripts
--           -- and stay between a and b
--           let k : C∞ := match max_subscript x q.right with
--           | some m := if 1 < n then min (min (i.2⁻¹) (b * m⁻¹)) n else min (i.2⁻¹) (b * m⁻¹)
--           | none   := if 1 < n then max i.2⁻¹ n else i.2⁻¹
--           end in
--           HNN_normalize_core
--             (reduce_mul ((conj_P t k (P.trans p q)), n * k⁻¹) l₁)
--             (let m := i.2 * k in
--               if m = 1 then l₂ else ⟨t, m⟩ :: l₂)
--           end
--     else HNN_normalize_core ((⟨p.left, p.right * of' (i.1, 1) i.2⟩, n) :: l₁) l₂

def HNN_normalize_single_pos (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  C∞ × P (free_group (ι × C∞)) → option (C∞ × P (free_group (ι × C∞)) × C∞)
| (n, p) :=
  match hs r' {s | s ≠ (x, b)} p.right with
  | none   := none
  | some q :=
    -- k is the maximum amount I can subtract from the subscripts
    -- and stay between a and b
    let k : C∞ := match max_subscript x q.right with
    | some m := min n (b * m⁻¹)
    | none   := n
    end in let m := n * k⁻¹ in some (m, conj_P t k (p.trans q), k)
  end

def HNN_normalize_single_neg (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  C∞ × P (free_group (ι × C∞)) → option (C∞ × P (free_group (ι × C∞)) × C∞)
| (n, p) :=
  match hs r' {s | s ≠ (x, a)} p.right with
  | none   := none
  | some q :=
    -- k is the minimum amount I can subtract from the subscripts
    -- and stay between a and b
    let k : C∞ := match min_subscript x q.right with
    | some m := max n (a * m⁻¹)
    | none   := n
    end in let m := n * k⁻¹ in some (m, conj_P t k (p.trans q), k)
  end

def HNN_normalize_single (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  C∞ × P (free_group (ι × C∞)) → option (C∞ × P (free_group (ι × C∞)) × C∞)
| (n, p) :=
  if 1 ≤ n
    then HNN_normalize_single_pos t x r' a b hs (n, p)
    else HNN_normalize_single_neg t x r' a b hs (n, p)

-- @[inline] meta def HNN_normalize'_core
--   (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
--   (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
--   list (C∞ × P (free_group (ι × C∞))) →
--   P (free_group (ι × C∞)) → C∞ →
--   list (Σ i : ι, C∞) →
--   list (C∞ × P (free_group (ι × C∞)))
-- | []           q m [] := [(m, q)]
-- | []           q m (i::l₂) :=
--   if i.1 = t
--     then HNN_normalize'_core [] q (m * i.2)  l₂
--     else if m = 1
--       then HNN_normalize'_core [] (q * inr (of_list [⟨(i.1, 1), i.2⟩])) 1 l₂
--       else HNN_normalize'_core [(m, q)] (inr (of_list [⟨(i.1, 1), i.2⟩])) 1 l₂
-- | ((n, p)::l₁) q m []      :=
--   match HNN_normalize'_single t x r' a b hs (n, q) with
--   | none          := (m, q)::(n, p)::l₁
--   | some (n', q') :=
--     if n' = 1
--       then HNN_normalize'_core l₁ (p * q') (n * m) []
--       else HNN_normalize'_core ((n', p)::l₁) q' (n * n'⁻¹ * m) []
--   end
-- | ((n, p)::l₁) q m (i::l₂) :=
--   if m = 1
--     then if i.1 = t
--       then HNN_normalize'_core ((n, p)::l₁) q i.2 l₂
--       else HNN_normalize'_core ((n, p)::l₁) (q * inr (of_list [⟨(i.1, 1), i.2⟩])) 1 l₂
--     else
--       match HNN_normalize'_single t x r' a b hs (n, q) with
--       | none :=  HNN_normalize'_core ((m, q)::(n,p)::l₁) 1 1 (i::l₂)
--       | some (n', q') :=
--         if n' = 1
--           then HNN_normalize'_core l₁ (p * q') (n * m) (i::l₂)
--           else HNN_normalize'_core ((n', p)::l₁) q' (n * n'⁻¹ * m) (i::l₂)
--       end

-- @[inline] meta def HNN_normalize' (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
--   (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
--   (w : free_group ι) : option (C∞ × P (free_group (ι × C∞))) :=
-- match HNN_normalize'_core t x r' a b hs [] 1 1 w.to_list with
-- | []               := some 1
-- | [(n, p)]         := some (n, p)
-- | (a::b::l)        := none
-- end

-- /-- Given a word `w` in `free_group ι`, `HNN_normalize` checks whether it
-- can be written in the form `t^n * g`, with `g` a `t`-free word in the
-- HNN extension. If it cannot be written in this form `HNN_normalize` returns `none`,
-- if it can then `HNN_normalize` returns this pair, along with a proof. More precisely,
-- it returns a pair `(p, n)` where `p` is a certificate that `t^(-n) * w` is equal
-- to a `t`-free term.  -/
-- @[inline] meta def HNN_normalize (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
--   (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
--   (w : free_group ι) : option (P (free_group (ι × C∞)) × C∞) :=
-- match HNN_normalize_core t x r' a b hs [] w.to_list with
-- | []        := some 1
-- | [a]       := some a
-- | (a::b::l) := none
-- end

/-- `reduce_mul (p, n) l`, returns `l * n * p` if `l`is thought
of as an element of the binary coproduct of `P (free_group (ι × C∞))` and `C∞`. -/
def reduce_mul_reversed :
  list (C∞ × P (free_group (ι × C∞)) × C∞) →
  C∞ × P (free_group (ι × C∞)) →
  list (C∞ × P (free_group (ι × C∞)) × C∞)
| [] p  := [(p.1, p.2, p.1)]
| ((m, q, s)::l) (n, p)  :=
  if n = 1
    then (m, q * p, s) :: l
    else (n, p, n * s) :: (m, q, s) :: l

-- def reduce_mul :
--   C∞ × P (free_group (ι × C∞)) →
--   list (C∞ × P (free_group (ι × C∞)) × C∞) →
--   list (C∞ × P (free_group (ι × C∞)) × C∞)
-- | p []  := [(p.1, p.2, p.1)]
-- | (n, p) ((m, q, s)::l) :=
--   if m = 1
--     then (m, p * q, s) :: l
--     else (n, p, n * s) :: (m, q, s) :: l

meta def HNN_normalize_initial_core
  (t x : ι) (a b : C∞) :
  list (C∞ × P (free_group (ι × C∞)) × C∞) → --reversed  and HNN normalized
  C∞ →
  P (free_group (ι × C∞)) →
  list (Σ i : ι, C∞) →
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ --reversed
| l₁ n p [] :=
  match HNN_normalize_single t x 1 a b
    (λ _ T _ w, by exactI guard (mem_closure_var T w) >> return (inr w)) (n, p) with
  | none             := (reduce_mul_reversed l₁ (n, p), 1)
  | some (n', q', m) := (reduce_mul_reversed l₁ (n', q'), m)
  end
| l₁ n₁ p (⟨i, n₂⟩::l₂) :=
  if i = t
    then
      match HNN_normalize_single t x 1 a b
        (λ _ T _ w, by exactI guard (mem_closure_var T w) >> return (inr w)) (n₁, p) with
      | none              :=
        HNN_normalize_initial_core
          (reduce_mul_reversed l₁ (n₁, p))
          n₂
          1
          l₂
      | some (n₁', q', m) :=
        HNN_normalize_initial_core
          (reduce_mul_reversed l₁ (n₁', p))
          (m * n₂)
          1
          l₂
      end
    else HNN_normalize_initial_core
      l₁
      n₁
      (p * inr (of_list [⟨(i, 1), n₂⟩]))
      l₂

meta def HNN_normalize_initial (t x : ι) (a b : C∞) (w : free_group ι) :
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ --normal
  :=
(HNN_normalize_initial_core t x a b [] 1 1 w.to_list).map list.reverse id

def reduce_mul_long  :
  list (C∞ × P (free_group (ι × C∞)) × C∞) → --reversed
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ → --normal
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞   --normal
| [] l₂ := l₂
| l₁ ([], n) := (l₁.reverse, n)
| ((n₁, p₁, s₁)::l₁) (((n₂, p₂, s₂)::l₂), n) :=
  if n₂ = 1
    then (l₁.reverse_core ((n₁, p₁ * p₂, s₂)::l₂), n)
    else (l₁.reverse_core ((n₁, p₁, s₁)::(n₂, p₂, s₂)::l₂), n)

@[inline] def normalized_mul :
  C∞ →
  P (free_group (ι × C∞)) →
  C∞ →
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ → --normal
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞   --normal
| m p n ([], d) := ([(m, p, m)], n * d)
| m p n (((k, q, s)::l), d) :=
  if n * k = 1
    then ((m, p * q, s)::l, d)
    else ((m, p, s * (n * k)⁻¹) :: (n * k, q, s) :: l, d)

@[inline] def reduce_mul_middle :
  list (C∞ × P (free_group (ι × C∞)) × C∞) → --reversed
  C∞ →
  P (free_group (ι × C∞)) →
  C∞ →
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ → -- normal order
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞  -- normal order
| [] m p n l := normalized_mul m p n l
| ((k, q, s)::l₁) m p n ([], d) :=
  if m = 1
    then (l₁.reverse_core [(k, q * p, s)], n * d)
    else (l₁.reverse_core [(k, q, s), (m, p, s * m)], n * d)
| ((k₁, q₁, s₁)::l₁) m p n (((k₂, q₂, s₂)::l₂), d) :=
  reduce_mul_long l₁ (normalized_mul m p n (((k₂, q₂, s₂)::l₂), d))

def find_peak_pos (l : list (C∞ × P (free_group (ι × C∞)) × C∞)) :
  ℕ × C∞ × P (free_group (ι × C∞)) × C∞ :=
l.foldl_with_index
  (λ i y p, if p.2.2 > y.2.2.2
    then (i, p.1, p.2.1, p.2.2)
    else y)
  (0, 1, 1, 1)

def find_peak_neg (l : list (C∞ × P (free_group (ι × C∞)) × C∞)) :
  ℕ × C∞ × P (free_group (ι × C∞)) × C∞ :=
l.foldl_with_index
  (λ i y p, if p.2.2 < y.2.2.2
    then (i, p.1, p.2.1, p.2.2)
    else y)
  (0, 1, 1, 1)

meta def HNN_normalize_core
  (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T) :
  list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ → --normal
  option (list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞)   --normal
| ([], d)     := some ([], d)
| ((μ::l), d) :=
  if μ.1 ≥ 1
    then let (i, n, p, s) := find_peak_pos (μ::l) in
      do (m, q, k) ← HNN_normalize_single_pos t x r' a b hs (n, p),
      HNN_normalize_core
        (reduce_mul_middle
          ((μ::l).take i).reverse
          m q k
          ((μ::l).drop (i+1), d))
    else let (i, n, p, s) := find_peak_neg (μ::l) in
      do (m, q, k) ← HNN_normalize_single_neg t x r' a b hs (n, p),
      HNN_normalize_core
        (reduce_mul_middle
          ((μ::l).take i).reverse
          m q k
          ((μ::l).drop (i+1), d))

meta def HNN_normalize (t x : ι) (r' : free_group (ι × C∞)) (a b : C∞)
  (hs : Π (r : free_group (ι × C∞)) (T : set (ι × C∞)) [decidable_pred T], solver r T)
  (w : free_group ι) :
  option (P (free_group (ι × C∞)) × C∞) :=
let w' : list (C∞ × P (free_group (ι × C∞)) × C∞) × C∞ :=
  HNN_normalize_initial t x a b w in
do l ← HNN_normalize_core t x r' a b hs w',
  match l with
  | ([], d)                      := some (1, d)
  | ([(n, p, s)], d)             :=
    guard (n = 1) >> return (p, d)
  | _ := none
  end
