import exp_sum_eq_zero
import base_case
import choose_letters
import no_exp_sum_zero
import solve_by_subst
import no_letters
import golf

open semidirect_product

meta def solve : Π ⦃ι : Type⦄ [decidable_eq ι]
  (r : free_group ι) (T : set ι) [decidable_pred T],
  by exactI solver r T :=
λ ι _ r T _ w, by exactI
  let vars_w := vars w in
  -- heuristic; algorithm is still complete without this line below
  (guard (vars_w.all (∈ T)) >> return (inr w)) <|>
  let (c₁, cyc_r) := cyclically_reduce r in
  P.change_r c₁ <$>
  match cyc_r with
  | ⟨[], _⟩ := by exactI guard (mem_closure_var T w) >> some (inr w)
  | ⟨[⟨r₁, r₂⟩], _⟩ := by exactI base_case_solver T r₁ r₂ w
  | cyc_r := by exactI
      -- heuristic; algorithm is still complete wihout below line. Without trying
      -- `guard (vars_w.all (∈ T)) >> return (inr w))` first,
      -- below line would break completeness.
    let vars_cyc_r := vars cyc_r in
    guard (vars_cyc_r.all (λ i, i ∈ vars_w ∨ i ∈ T)) >>
      -- heuristic; algorithm is still complete without this line below
      -- solve_by_subst seems to usually make it slower, but maybe worth doing anyway if it is
      -- a lot faster in some cases
    solve_by_subst T cyc_r w <|>
    match choose_t_and_x cyc_r T vars_cyc_r with
      | none := no_letters T r (by exactI solve r ∅) w
      | some ((t, α), (x, β)) :=
        if α = 1
          then exp_sum_eq_zero T t x     (λ r T _, by exactI solve r T) cyc_r w
          else exp_sum_ne_zero T t x α β (λ r T _, by exactI solve r T) cyc_r w
      end
  end

meta def golf_solve ⦃ι : Type⦄ [decidable_eq ι] [has_lt ι] [decidable_rel ((<) : ι → ι → Prop)]
  (r : free_group ι) (T : set ι) [decidable_pred T] : solver r T :=
λ w, (golf₂ r ∘ golf₁ r) <$> solve r T w

set_option profiler true

variables {ι : Type} [decidable_eq ι] [has_lt ι] [decidable_rel ((<) : ι → ι → Prop)] (T : set ι)

meta def test (r : free_group ι) (T : set ι) [decidable_pred T] (w : free_group ι) : bool :=
match golf_solve r T w with
| some p' := P.lhs r p' = w ∧ mem_closure_var T p'.right
| none := ff
end

open free_group

#eval test (of 0 * of 1 * (of 0)⁻¹) ∅ (of 0 * of 1 * (of 0)⁻¹)

--#eval solve (of 0 ^ 88 * of 1 ^ 88) {1} (of 0 * of 1 * (of 0)⁻¹)

#eval test (of 0 * of 1) ∅ (of 0 * (of 1) * (of 0)⁻¹ * (of 1)⁻¹)
-- #eval ((solve (of 0 * of 1) ∅
--             (of 0 * (of 1) * (of 0)⁻¹ * (of 1)⁻¹)).is_some)

#eval test (of 0 * of 1 * (of 0)⁻¹ * (of 1)⁻¹) ∅
  (of 0 ^ 2 * (of 1)⁻¹ ^ 2 * (of 0)⁻¹ ^ 2 * (of 1) ^ 2)

-- #eval (solve (of 0 * of 1 * (of 0)⁻¹ * (of 1)⁻¹) ∅
--             (of 0 ^ 2 * (of 1)⁻¹ ^ 2 * (of 0)⁻¹ ^ 2 * (of 1) ^ 2)).iget.left

#eval test (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹) ∅
  (of "a" ^ 2 * (of "b") * (of "a")⁻¹ ^ 2 * (of "b")⁻¹)
--P.lhs (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹)
--free_group.map (golf_single (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹))
-- ((solve (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹) ∅
--     (of "a" ^ 2 * (of "b") * (of "a")⁻¹ ^ 2 * (of "b")⁻¹)).iget)

#eval let r := of 0 * of 1 * (of 0)^(-3 : ℤ) * (of 1)^4 in
  test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r)
  --(solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r)).iget.left

#eval let r := of 0 * of 1 * (of 0)^(-5 : ℤ) * (of 1)^4 in
  (test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r))

#eval let r := of 0 * of 1 * (of 0)^(-5 : ℤ) * (of 1)^4 in
(of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r)

-- #eval let r := of 0 * of 1 * (of 0)^(-11 : ℤ) * (of 1)^4 in
--   (solve r ∅ (of 0 ^ 10 * of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
--     * r⁻¹ * (of 0)⁻¹ * r * of 0 ^ (-10 : ℤ))⁻¹).iget.left.to_list.length

#eval let r := of 0 * of 1 * (of 0)^(-9 : ℤ) * (of 1)^6 in
  (solve r {0} (of 0 ^ 7 * of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r)⁻¹).iget.left.to_list.length

#eval let r := (of 0 ^ 20 * of 1 ^ 11)^2 in
  solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r)

def r : free_group ℕ := (of 0 ^ 5 * of 1 ^ 5)^2


#eval let r := (of 0 ^ 7 * of 1 ^ 3)^2 in --BUG
(solve r ∅ r)


open multiplicative
#eval choose_t_and_x r ∅ [0, 1]
#eval ((cyclically_conjugate 0 r).2 = r : bool)
#eval add_subscript 1
  (psi 1 0 (of_add 6) (of_add 6) r)
def r₁ := (add_subscript 1
  (psi 1 0 (of_add 6) (of_add 6) r)).left

#eval (psi 1 0 (of_add 6) (of_add 6) r).to_list
#eval HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T) []
  [⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩]

meta def Z := HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  [(⟨1, of_list [⟨(0, 1), of_add 1⟩]⟩, 1)]
  [⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩]

#eval solve r₁ { x | x ≠ (0, of_add 0) } (of_list [⟨(0, 1), of_add 1⟩])

#eval HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  [(1, of_add (-6)), (⟨1, of_list [⟨(0, 1), of_add 1⟩]⟩, 1)]
  [⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩]

#eval (HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  [(inr (of_list [⟨(0, of_add 0), of_add 1⟩]), of_add (-6)),
    (⟨1, of_list [⟨(0, 1), of_add 1⟩]⟩, 1)]
  [⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩])

#eval (HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  [(1, of_add (-6)), (inr (of_list [⟨(0, of_add 0), of_add 1⟩]), of_add (-6)),
    (⟨1, of_list [⟨(0, 1), of_add 1⟩]⟩, 1)]
  [⟨0, of_add 1⟩, ⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩])

#eval (HNN_normalize_core 1 0
  (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  [(inr (of_list [⟨(0, of_add 0), of_add 1⟩]), of_add (-6)),
   (inr (of_list [⟨(0, of_add 0), of_add 1⟩]), of_add (-6)),
    (⟨1, of_list [⟨(0, 1), of_add 1⟩]⟩, 1)]
  [⟨1, of_add 12⟩, ⟨0, of_add 1⟩,
    ⟨1, of_add (-6)⟩, ⟨0, of_add 1⟩, ⟨1, of_add (-6)⟩,
    ⟨0, of_add 1⟩, ⟨1, of_add 12⟩] = Z: bool)

#eval show C∞, from
  match solve r₁ {x | x ≠ (0, of_add (-12))} (of_list [⟨(0, of_add 0), of_add 1⟩]) with
  | none := sorry
  | some q := let k : C∞ :=
    match min_subscript 0 q.right with
    | some m := max ((of_add 12)⁻¹) ((of_add (-12)) * m⁻¹)
    | none   := (of_add 12)⁻¹
    end in k
  end


#eval HNN_normalize 1 0 (add_subscript 0 (psi 1 0 (of_add 6) (of_add 6) r)).left
    (of_add (-12)) (of_add 0)
  (λ r T _, by exactI solve r T)
  (psi 1 0 (of_add 6) (of_add 6) r)

def r' := (add_subscript 1 (psi 1 0 (of_add 4) (of_add 4) r)).left

#eval choose_t_and_x r' ∅ (vars r')
def r₂ := (add_subscript (0, of_add (0 : ℤ))
  (psi (0, of_add 0) (0, of_add (-4 : ℤ)) (of_add 2) (of_add 2) r')).left

#eval r₂
#eval base_case_solver ∅ ((0, of_add (-4 : ℤ)), of_add (2 : ℤ)) (of_add (-2 : ℤ)) r₂

#eval let r := of 0 * of 1 * (of 0)^(-17 : ℤ) * (of 1)^5 in
  (test r ∅ ((of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r))⁻¹)

#eval let r := of 0 * of 1 * (of 0)^(-1 : ℤ) * (of 1)^1 in
let w := (of 2 * r * (of 2)⁻¹ * of 1 * r * (of 1)⁻¹ * r⁻¹ *
  (of 0) * r⁻¹ * (of 0)⁻¹ * r * of 2 * r * (of 2)⁻¹) in
  test r {x | x ≠ 2} w.

-- #eval solve (of 0 * of 1) (of 0 * of 1 * )


#eval let r := (of 0)^1 * of 1 * (of 0)^(-2 : ℤ) * (of 1)^(-1 : ℤ) in
  (test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r))
  -- (P.lhs r
  --   (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget =
  -- (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r) : bool)

#eval let r := (of 'a') ^ (-2 : ℤ) in
test r ∅ ((of 'a') ^ 22)

#eval let r := (of 'a') ^ (-2 : ℤ) in
test r {'b'} ((of 'a') ^ 22 * of 'b' * of 'a' ^ (-10 : ℤ) * (of 'b'))

#eval let r := (1 : free_group ℕ) in test r {0} 1

#eval let r := (1 : free_group ℕ) in test r ∅ 1

#eval let r := of 0 * of 1 * (of 0)⁻¹ * (of 1) in
test r {x | x = 1 ∨ x = 2}
  (of 1 * r * (of 1) * r⁻¹ * of 2 * (of 1) * (of 0) * r⁻¹ * (of 0)⁻¹ * r * of 1)

#eval let r := of 0 * of 1 * (of 0) * (of 1)^2 in
test r ∅ (of 0 * of 1 * (of 1 * of 0)⁻¹)

#eval let r := of 0 * of 1 * of 0 * of 1 * (of 0)^2 * of 1 in
test r ∅ ((of 0) * (of 1) * (of 0)⁻¹ * (of 1)⁻¹)

#eval let r := of 0 * of 1 * (of 0) ^ 3 * (of 1) ^ (4 : int) in
test r {0} (of 0 * r * (of 1)⁻¹ * r * (of 1) * r)

#eval choose_t_and_x (of 0 * of 1 * (of 0) ^ 3 * (of 1) ^ (4 : int)) {0} [0, 1]

#eval let r := (of 0) * of 1 * (of 0)^(-1 : ℤ) * (of 1)^(2 : ℤ) in
test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)

#eval let r := (of 0 * (of 1)^2)^8 in
test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)

#eval let r := (of 0 * (of 1)^2)^2 in
test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)

#eval let r := of 0 * of 1 * of 0 * of 1 * (of 0)^2 * of 1 in
test r ∅ (of 1 ^ 3 * of 0 ^ 4)⁻¹

-- #eval let r := (of 0 * (of 1) * (of 0)⁻¹ * of 1)^2 in
--   (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget.left.to_list.length

def w : ℕ → free_group char
| 0 := of 'a'
| (n+1) := ((of 'b')⁻¹ * w n * of 'b')⁻¹ * of 'a' * ((of 'b')⁻¹ * w n * of 'b')

--#print string.decidable_eq
#eval test (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 3)
#eval P.lhs  (w 1 * (of 'a') ^ (2 : ℤ))
  (golf_solve (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 2)).iget
#eval w 2
#eval (of 'b')⁻¹ * (of 'a')^(2 : ℤ)

--#eval (golf_solve (w 1 * (of 'a') ^ (2 : ℤ)) {'a'} (w 2)) --HARD
#eval choose_t_and_x (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (vars (w 1 * (of 'a') ^ (-2 : ℤ)))

#eval (golf_solve
  (w 1 * (of 'a') ^ (-2 : ℤ))
  ⊥
  ((of 'a') * w 3 * (of 'a')⁻¹ * (w 3)⁻¹)).iget.left.to_list.length

open multiplicative
