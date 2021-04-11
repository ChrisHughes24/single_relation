import solve tactic.group

open expr tactic free_group

local notation `C∞` := multiplicative ℤ

meta structure cache :=
(G : expr)
(univ : level)
(red : transparency)
(ic : ref instance_cache) -- instance_cache for G
(atoms : ref (buffer expr))

@[derive [monad, alternative]]
meta def group1r_m (α : Type) : Type :=
reader_t cache tactic α

namespace group1r

meta def get_cache : group1r_m cache := reader_t.read

/-- Run a `group1r_m` tactic in the tactic monad. -/
meta def group1r_m.run (red : transparency) (G : expr)
  {α} (m : group1r_m α) : tactic α :=
do u ← mk_meta_univ,
   infer_type G >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   ic ← mk_instance_cache G,
   zc ← mk_instance_cache `(ℤ),
   using_new_ref ic $ λ ric,
   using_new_ref mk_buffer $ λ atoms,
   reader_t.run m ⟨G, u, red, ric, atoms⟩

namespace group1r_m

meta def lift {α : Type} : tactic α → group1r_m α := reader_t.lift

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This version
is abstract over the instance cache in question (either the ring `α`, or `ℕ` for exponents). -/
@[inline] meta def ic_lift' (icf : cache → ref instance_cache) {α}
  (f : instance_cache → tactic (instance_cache × α)) : group1r_m α :=
⟨λ c, do
  let r := icf c,
  ic ← read_ref r,
  (ic', a) ← f ic,
  a <$ write_ref r ic'⟩

/-- Lift an instance cache tactic (probably from `norm_num`) to the `group1r_m` monad. This uses
the instance cache corresponding to the ring `α`. -/
@[inline] meta def ic_lift {α} : (instance_cache → tactic (instance_cache × α)) → group1r_m α :=
ic_lift' cache.ic

meta def add_atom (e : expr) : group1r_m ℕ :=
⟨λ l, do es ← read_ref l.atoms,
  es.iterate failed (λ n e' t, t <|> (is_def_eq e e' l.red $> n.1)) <|>
    (es.size <$ write_ref l.atoms (es.push_back e))⟩

/-- Get an already encountered atom by its index. -/
meta def get_atom (n : ℕ) : group1r_m expr :=
⟨λ c, do es ← read_ref c.atoms, pure (es.read' n)⟩

meta def to_free_group : expr → group1r_m (free_group ℕ)
| `(%%a * %%b) :=
  do a' ← to_free_group a,
     b' ← to_free_group b,
     return (a' * b')
| `((%%a)⁻¹) :=
  do a' ← to_free_group a, return (a'⁻¹)
| `(@has_one.one _ _) := return 1
| e@`((%%a) ^ (-%%n)) :=
  cond (is_numeral n)
    (do ne ← lift (eval_expr' ℤ n),
      a' ← to_free_group a,
      return (a' ^ -ne))
    (do i ← add_atom e, return (of i))
| e@`((%%a) ^ (%%n)) :=
  cond (is_numeral n)
    ((do ne ← lift (eval_expr' ℕ n),
      a' ← to_free_group a,
      return (a' ^ ne)) <|>
      (do ne ← lift (eval_expr' ℤ n),
        a' ← to_free_group a,
        return (a' ^ ne)))
    (do i ← add_atom e, return (of i))
| e := do i ← add_atom e, return (of i)

-- meta def to_group_equality : expr → group1r_m (expr × free_group ℕ × free_group ℕ)
-- | `(@eq %%G %%a %%b) :=
--   do a' ← to_free_group a,
--      b' ← to_free_group b,
--      return (G, a', b')
-- | _ := failure

-- meta def X : has_reflect int := reflect n
-- #print int.has_reflect
-- set_option pp.numerals false

-- run_cmd tactic.trace (X (-12))

protected meta def expr.of_nat (n : ℕ) : expr :=
if n = 0 then `(0 : ℤ) else
  let one := `(1 : ℤ) in
  n.binary_rec one $ λ b n e,
    if n = 0 then one else
    cond b
      `((bit1 %%e : ℤ))
      `((bit0 %%e : ℤ))

protected meta def expr.of_int : ℤ → expr
| (n : ℕ) := expr.of_nat n
| -[1+ n] := `(has_neg.neg %%(expr.of_nat (n + 1)) : ℤ)

meta def free_group_to_expr_aux : list (Σ i : ℕ, C∞) → group1r_m expr
| []            := ic_lift $ λ ic, ic.mk_app ``has_one.one []
| (⟨a, n⟩ :: l) :=
  do w ← free_group_to_expr_aux l,
  ae ← get_atom a,
  lift $
  do p ← tactic.mk_app `has_pow.pow [ae, expr.of_int n.to_add],
    tactic.mk_app `has_mul.mul [p, w]

meta def free_group_to_expr : free_group ℕ → group1r_m expr :=
free_group_to_expr_aux ∘ subtype.val

meta def free_group_free_group_to_expr_aux : list (Σ i : free_group ℕ, C∞) → group1r_m expr
| [] := do c ← get_cache,
  return (app (const `list.nil [level.max c.univ level.zero])
    (app (app (const `prod [c.univ, level.zero]) c.G) `(ℤ)))
| (⟨w, n⟩ :: l) :=
  do w' ← free_group_to_expr w,
  l' ← free_group_free_group_to_expr_aux l,
  c ← get_cache, lift $
  do w'n ← tactic.mk_app `prod.mk [w', expr.of_int n.to_add],
  tactic.mk_app `list.cons [w'n, l']

def eval_conj {G : Type*} [group G] (r : G) : list (G × ℤ) → G
| []          := 1
| (a::l) := a.1 * (r ^ a.2 * (a.1⁻¹ * eval_conj l))

lemma eval_conj_eq_one {G : Type*} [group G] (r : G) (hr : r = 1) : ∀ (l : list (G × ℤ)),
  eval_conj r l = 1
| []          := rfl
| (⟨g, n⟩::l) := by rw [eval_conj, eval_conj_eq_one, hr]; simp [*, eval_conj]

lemma mul_inv_eq_one_of_eq {G : Type*} [group G] (a b : G) (h : a = b) : a * b⁻¹ = 1 :=
by simp [h]

meta def free_group_free_group_to_expr (p : free_group (free_group ℕ))
  (r : expr) (r_eq_one : expr) : group1r_m expr :=
free_group_free_group_to_expr_aux p.to_list

/- What do I have left?

-/

end group1r_m

open group1r.group1r_m group1r

meta def mk_list
  (hyp : expr)
  (hyp_type : expr)
  (tgt : expr)
  (red : transparency) :
  -- first expr is an expr of type `list (G × ℤ)`
  -- second expr is a proof of r = 1
  tactic (expr × expr) :=
do (hyp_left, hyp_right) ← is_eq hyp_type,
  (tgt_left, tgt_right) ← is_eq tgt,
  G ← infer_type hyp_left,
  group1r_m.run red G $
  do hyp_lhs ← to_free_group hyp_left,
  hyp_rhs ← to_free_group hyp_right,
  tgt_lhs ← to_free_group tgt_left,
  tgt_rhs ← to_free_group tgt_right,
  r ← ic_lift (λ ic,
    do (ic, right_inv) ← ic.mk_app `has_inv.inv [hyp_right],
    ic.mk_app `has_mul.mul [hyp_left, right_inv]),
  r_eq_one ← ic_lift
    (λ ic, ic.mk_app `group1r.group1r_m.mul_inv_eq_one_of_eq [hyp_left, hyp_right, hyp]),
  p ← group1r_m.lift (_root_.golf_solve (hyp_lhs * hyp_rhs⁻¹) ∅ (tgt_lhs * tgt_rhs⁻¹)),
  group1r_m.lift $ tactic.trace (repr (list.map (λ x : Σ i : free_group ℕ, C∞, x.snd.nat_abs) p.left.1).sum),
  l ← free_group_free_group_to_expr p.left r r_eq_one,
  return (l, r_eq_one)

lemma helper {G : Type*} [group G] {r : G} (hr : r = 1) {a b : G} (l : list (G × ℤ)) :
  a = eval_conj r l * b → a = b :=
by { rw [eval_conj_eq_one r hr, one_mul], exact id }

end group1r

namespace tactic.interactive

open lean.parser lean interactive.types interactive group1r tactic.simp_arg_type

local postfix `?`:9001 := optional

meta def group1r (red : parse (lean.parser.tk "!")?) (hyp : parse (tk "using" *> texpr)) :
  tactic unit :=
do hyp ← (hyp : option pexpr) >>= i_to_expr,
   let transp := if red.is_some then semireducible else reducible,
   hyp_type ← infer_type hyp,
   tgt ← target,
   (l, r_eq_one) ← mk_list hyp hyp_type tgt transp,
   `[refine group1r.helper %%r_eq_one %%l _,
     simp only [group1r.group1r_m.eval_conj, gpow_bit0,
      gpow_bit1, one_mul, mul_one, mul_inv_rev, mul_assoc,
      gpow_neg, mul_inv_self, inv_mul_self,
      one_inv, mul_inv_cancel_left, inv_mul_cancel_left,
      gpow_one, gpow_zero, pow_bit0, pow_bit1, pow_one, inv_inv]]

end tactic.interactive

set_option pp.implicit true
set_option profiler true

-- example {G : Type*} [group G] {a b c : G}
--   (h : (a * b) * (b^2 * a * c) * (a * b)⁻¹ = (b^2 * a * c)^2) :
--   (a * b)^5 * (b^2 * a * c) * (a * b)^(-5 : int) * (b^2 * a * c) =
--   (b^2 * a * c) * (a * b)^5 * (b^2 * a * c) * (a * b)^(-5 : int) :=
-- begin
--   group1r using h,
-- end
set_option profiler true
-- example {G : Type*} [group G] (a b : G)
--   (h : a * b * a^(-11 : int) * b^ 4 = 1) :
--   a^10 * b^(-4 : int) * a^11 * b⁻¹ * a * b * a^(-11 : int) * b^5 * a^(-11 : int)
--   * b * a^(11 : int) * b⁻¹ * a⁻¹ * b⁻¹ * a^(-10 : int) = 1 :=
-- begin
--   group1r using h,

-- end


example {G : Type} [group G] (a b c d : G) (h : a * b * c * a * b^2 = 1)
  (h2 : a * b * d * a * b * c^(-2 : int) = 1) :
  a * b * d * a * b = (b⁻¹ * a⁻¹ * b^(-2 : int) * a⁻¹)^(2 : int) :=
have d = b⁻¹ * a⁻¹ * (a * b * c^(-2 : int))⁻¹, by group1r using h2,
begin
  subst this,
  group1r using h,

end


example {G : Type*} [group G] {a b c : G} (m : nat)
  (h : a * b * a⁻¹ = b^2) (n : nat) : a ^ n * b = b ^ (2^n) * a^n :=
begin
  induction n with n ih,
  { norm_num },
  { simp only [pow_succ, mul_comm 2],
    simp only [pow_mul], }

end

def W {G : Type*} [group G] (a b : G): ℕ → G
| 0 := a
| (n+1) := (b⁻¹ * W n * b)⁻¹ * a * (b⁻¹ * W n * b)

example {G : Type*} [group G] (a b : G)
  (h : (b⁻¹ * a * b)⁻¹ * a * (b⁻¹ * a * b) = a ^ 2) :
  W a b 2 = a ^ 4 :=
begin
  dunfold W,
  simp [mul_assoc, gpow_bit0, gpow_bit1],
  group1r using h,

end
