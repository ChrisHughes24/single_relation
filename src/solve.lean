import exp_sum_eq_zero
import base_case
import choose_letters
import no_exp_sum_zero
import solve_by_subst
import no_letters
import golf

open semidirect_product

-- Fix this. Did not consider case when `cyc_r` has length 1 but not `r`.
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
      -- `solve_by_trivial` first, below line would break completeness.
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
let p := golf_solve r T w in
∃ h : p.is_some,
  let p' := option.get h in
  P.lhs r p' = w ∧ mem_closure_var T p'.right

open free_group

#eval test (of 0 * of 1 * (of 0)⁻¹) ∅ (of 0 * of 1 * (of 0)⁻¹)

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
  (test  r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r))

#eval let r := of 0 * of 1 * (of 0)^(-5 : ℤ) * (of 1)^4 in
(of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r)

-- #eval let r := of 0 * of 1 * (of 0)^(-11 : ℤ) * (of 1)^4 in
--   (golf_solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
--     * r⁻¹ * (of 0)⁻¹ * r)).iget.left.to_list.length

-- #eval let r := of 0 * of 1 * (of 0)^(-9 : ℤ) * (of 1)^6 in
--   (golf_solve r {0} (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
--     * r⁻¹ * (of 0)⁻¹ * r)).iget.left.to_list.length

#eval let r := of 0 * of 1 * (of 0)^(4 : ℤ) * (of 1)^3 in
  (golf_solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)
    * r⁻¹ * (of 0)⁻¹ * r)).iget.left.to_list.length

#eval let r := of 0 * of 1 * (of 0)^(-1 : ℤ) * (of 1)^1 in
  let w := (of 2 * r * (of 2)⁻¹ * of 1 * r *
      (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r * of 2 * r * (of 2)⁻¹) in
  test r {x | x ≠ 2} w.

-- #eval solve (of 0 * of 1) (of 0 * of 1 * )


#eval let r := (of 0)^1 * of 1 * (of 0)^(-2 : ℤ) * (of 1)^(-1 : ℤ) in
  (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget.left.to_list.length
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
golf_solve r ∅ (of 0 * of 1 * (of 1 * of 0)⁻¹)

#eval let r := of 0 * of 1 * of 0 * of 1 * (of 0)^2 * of 1 in
golf_solve r ∅ ((of 0) * (of 1) * (of 0)⁻¹ * (of 1)⁻¹)

-- #eval let r := of 0 * of 1 * (of 0) ^ 3 * (of 1) ^ (4 : int) in
--   (golf_solve r {0} (r * (of 1)⁻¹ * r * (of 1) * r)).iget.left

#eval choose_t_and_x (of 0 * of 1 * (of 0) ^ 3 * (of 1) ^ (4 : int)) ∅ [0, 1]

#eval let r := (of 0) * of 1 * (of 0)^(-1 : ℤ) * (of 1)^(2 : ℤ) in
  test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)

#eval let r := (of 0 * (of 1)^2)^8 in
  test r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)

#eval let r := (of 0 * (of 1)^2)^2 in
  (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget.left

#eval let r := of 0 * of 1 * of 0 * of 1 * (of 0)^2 * of 1 in
golf_solve r ∅ (of 0 ^ 4 * of 1 ^ 3)

#eval let r := (of 0 * (of 1) * (of 0)⁻¹ * of 1)^2 in
  (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget.left.to_list.length

#eval ('ℵ'.val)

def w : ℕ → free_group char
| 0 := of 'a'
| (n+1) := ((of 'b')⁻¹ * w n * of 'b')⁻¹ * of 'a' * ((of 'b')⁻¹ * w n * of 'b')

--#print string.decidable_eq
#eval test (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 3)
#eval test (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 2)
#eval test (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 1)
#eval choose_t_and_x (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (vars (w 1 * (of 'a') ^ (-2 : ℤ)))

#eval (golf_solve
  (w 1 * (of 'a') ^ (-2 : ℤ))
  (⊤)
  ((of 'a')^2 * w 3 * (of 'a')⁻¹ * (w 3)⁻¹ * (of 'a')⁻¹)).iget.left.to_list.length

open multiplicative
