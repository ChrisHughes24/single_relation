import exp_sum_eq_zero
import base_case
import choose_letters
import no_exp_sum_zero
import solve_by_trivial
import solve_by_subst
import no_letters

open semidirect_product
variables {ι : Type} [decidable_eq ι] (T : set ι)

-- Did I take into account the case when T is everything in r?
-- This rarely happens right? Unless it happens at the start
-- Proof assumes wlog every element of S appears in r, where is this used?
meta def solve : Π ⦃ι : Type⦄ [decidable_eq ι]
  (r : free_group ι) (T : set ι) [decidable_pred T],
  by exactI solver r T :=
λ ι _ r T _ w,
match r with
| ⟨[], _⟩ := by exactI
  if mem_closure_var T w
  then some (inr w)
  else none
| ⟨[⟨r₁, r₂⟩], _⟩ := by exactI base_case_solver T r₁ r₂ w
| r := by exactI
  let vars_w := vars w in
  solve_by_trivial T w vars_w <|> -- heuristic; algorithm is still complete without this line
  let (c₁, cyc_r) := cyclically_reduce r in
  P.change_r c₁ <$>
    -- heuristic; algorithm is still complete without this line below
    -- solve_by_subst seems to usually make it slower, but maybe worth doing anyway if it is
    -- a lot faster in some cases
  solve_by_subst T cyc_r w <|>
  if (vars (trace (repr $ cyc_r.to_list.length) cyc_r)).any (λ i, i ∉ vars_w ∧ i ∉ T)
    then none -- heuristic; algorithm is still complete without this line and above line
    else match choose_t_and_x cyc_r T with
      | none := no_letters T r (by exactI solve r ∅) w
      | some ((t, α), (x, β)) :=
        if α = 1
          then exp_sum_eq_zero T t x     (λ r T _, by exactI solve r T) cyc_r w
          else exp_sum_ne_zero T t x α β (λ r T _, by exactI solve r T) cyc_r w
      end
end

set_option profiler true

open free_group

#eval ((solve (of 0 * of 1) ∅
            (of 0 * (of 1) * (of 0)⁻¹ * (of 1)⁻¹)).is_some)

#eval (solve (of 0 * of 1 * (of 0)⁻¹ * (of 1)⁻¹) ∅
            (of 0 ^ 2 * (of 1)⁻¹ ^ 2 * (of 0)⁻¹ ^ 2 * (of 1) ^ 2)).iget.left

#eval --P.lhs (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹)
--free_group.map (golf_single (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹))
((solve (of "a" * of "b" * (of "a")⁻¹ * (of "b")⁻¹) ∅
    (of "a" ^ 2 * (of "b") * (of "a")⁻¹ ^ 2 * (of "b")⁻¹)).iget)

#eval let r := of 0 * of 1 * (of 0)^(-3 : ℤ) * (of 1)^4 in
  (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r)).iget.left

#eval let r := of 0 * of 1 * (of 0)^(-1 : ℤ) * (of 1)^2 in
  let w := (of 2 * r * (of 2)⁻¹ * of 1 * r *
      (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r * of 2 * r * (of 2)⁻¹) in
  ((solve r {x | x ≠ 2} w).iget.left)

-- #eval solve (of 0 * of 1) (of 0 * of 1 * )


#eval let r := of 0 * of 1 * (of 0)^(-100 : ℤ) * (of 1)^(4 : ℤ) in
  (P.lhs r
    (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget =
  (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r) : bool)

#eval let r := of 0 * of 1 * (of 0)^(-100 : ℤ) * (of 1)^(4 : ℤ) in
    (solve r ∅ (of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0)⁻¹ * r⁻¹ * (of 0) * r)).iget

#eval let r := of 0 * of 1 * (of 0)⁻¹ * (of 1) in
  of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r

#eval let r := of 0 * of 1 * (of 0)⁻¹ * (of 1) in
  (solve r ∅ ((of 1 * r * (of 1)⁻¹ * r⁻¹ * (of 0) * r⁻¹ * (of 0)⁻¹ * r))).iget.left

#eval let r := of 0 * of 1 * of 2 * of 3 in
  (solve r ∅ (of 1 * of 2 * of 3 * of 0)).iget.left

--set_option timeout 10000000000

def w : ℕ → free_group char
| 0 := of 'a'
| (n+1) := ((of 'b')⁻¹ * w n * of 'b')⁻¹ * of 'a' * ((of 'b')⁻¹ * w n * of 'b')

--#print string.decidable_eq
#eval --free_group.map (golf_single (w 1 * (of 'a') ^ (-2 : ℤ)))

  (solve (w 1 * (of 'a') ^ (-2 : ℤ)) {'a'} (w 3)).iget

-- #eval
-- let r := (of 'a' * of 'b')^2 in
-- (free_group.map (golf_single r)
-- (solve r ∅ ((of 'a' * r⁻¹ * (of 'a')⁻¹ * r)^44)).iget.left =
--   (solve r ∅ ((of 'a' * r⁻¹ * (of 'a')⁻¹ * r)^44)).iget.left  : bool)

open multiplicative
