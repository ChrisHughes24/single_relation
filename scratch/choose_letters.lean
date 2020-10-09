import for_mathlib.coprod.free_group data.list.min_max order.lexicographic

open free_group multiplicative

variables {ι : Type} [decidable_eq ι] [inhabited ι] (r : free_group ι)
variables (T : set ι) [decidable_pred T]

-- Want `x` to have least occurences in `w`
-- `t` with smallest `exp_sum`, tie break is large sum of nat_abs in `r`,

def vars : list ι := (r.to_list.map sigma.fst).erase_dup

def exp_sum_and_occs (i : ι) : C∞ × ℕ  :=
r.to_list.foldl
  (λ n j, if j.1 = i
    then (n.1 * j.2, n.2 + to_add j.2.nat_abs)
    else n)
  (1, 0)

def choose_t_and_x :
  (ι × C∞) × -- t and its exponent sum
  (ι × C∞)   -- x and its exponent sum.
  :=
let l := (vars r).map (λ i, (i, exp_sum_and_occs r i)) in
let t := (l.argmin (λ i : ι × (C∞ × ℕ), show lex ℕ (order_dual ℕ),
  from ((to_add i.2.1).nat_abs, i.2.2))).iget in
if t.2.1 = 1
  then if t.1 ∈ T
    then let x :=
      ((l.filter (λ p : ι × C∞ × ℕ, p.1 ∉ T)).argmin (λ i : ι × (C∞ × ℕ), i.2.2)).iget in
        ((t.1, 1), (x.1, x.2.1))
    else let x :=
      ((l.filter (λ p : ι × C∞ × ℕ, p.1 ≠ t.1)).argmin (λ i : ι × (C∞ × ℕ), i.2.2)).iget in
        ((t.1, 1), (x.1, x.2.1))
  else if t.1 ∈ T
    then let x :=
      ((l.filter (λ p : ι × C∞ × ℕ, p.1 ∉ T)).argmin (λ i : ι × (C∞ × ℕ), i.2.2)).iget in
        ((t.1, t.2.1), (x.1, x.2.1))
    else
      let x :=
        ((l.filter (λ p : ι × C∞ × ℕ, p.1 ∉ T)).argmin (λ i : ι × (C∞ × ℕ), i.2.2)).iget in
      let t' :=
        ((l.filter (λ p : ι × C∞ × ℕ, p.1 ≠ x.1)).argmin
          (λ i : ι × (C∞ × ℕ), show lex ℕ (order_dual ℕ),
            from ((to_add i.2.1).nat_abs, i.2.2))).iget in
      ((t'.1, t'.2.1), (x.1, x.2.1))
