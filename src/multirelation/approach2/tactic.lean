import .approach2
import tactic

namespace group_rel
open expr tactic free_group

#print tactic.mk_simp_set

meta structure cache :=
(G : expr)
(univ : level)
(red : transparency)
(ic : ref instance_cache) -- instance_cache for G
(atoms : ref (buffer expr))
(free_group_simp_lemmas : simp_lemmas)
(eval_simp_lemmas : simp_lemmas)

@[derive [monad, alternative]]
meta def group_rel_m (α : Type) : Type :=
reader_t cache tactic α

meta def get_cache : group_rel_m cache := reader_t.read

section

open tactic.simp_arg_type

/-
[inv_core, inv_def, bool.bnot_true, bool.bnot_false, eq_self_iff_true,
  true_and, and_true, one_def, mul_def, list.reverse_core, mul_aux, ne.def,
  not_false_iff, if_true, if_false, false_and, and_false,
  nat.succ.inj_eq, nat.zero_eq_succ_eq]
-/

meta def mk_free_group_simp_lemmas : tactic simp_lemmas :=
tactic.mk_simp_set tt []
  [expr ``(inv_core.equations._eqn_1),
  expr ``(inv_core.equations._eqn_2),
  expr ``(inv_def),
  expr ``(bool.bnot_true),
  expr ``(bool.bnot_false),
  expr ``(@eq_self_iff_true ℕ),
  expr ``(true_and),
  expr ``(and_true),
  expr ``(one_def),
  expr ``(mul_def),
  expr ``(@list.reverse_core.equations._eqn_1 (ℕ × bool)),
  expr ``(@list.reverse_core.equations._eqn_2 (ℕ × bool)),
  expr ``(mul_aux.equations._eqn_1),
  expr ``(mul_aux.equations._eqn_2),
  expr ``(mul_aux.equations._eqn_3),
  expr ``(ne.def),
  expr ``(not_false_iff),
  expr ``(if_true),
  expr ``(if_false),
  expr ``(false_and),
  expr ``(and_false),
  expr ``(nat.succ.inj_eq),
  expr ``(zero_eq_succ_eq),
  expr ``(succ_eq_zero_eq)]
>>= λ x, return x.fst

meta def mk_eval_simp_lemmas : tactic simp_lemmas :=
tactic.mk_simp_set tt []
  [expr ``(eval.equations._eqn_1),
   expr ``(eval.equations._eqn_2),
   expr ``(eval.equations._eqn_3),
   expr ``(nth.equations._eqn_1),
   expr ``(nth.equations._eqn_2),
   expr ``(nth.equations._eqn_3),
   expr ``(one_mul),
   expr ``(mul_one),
   expr ``(mul_assoc),
   expr ``(mul_inv_self),
   expr ``(inv_mul_self),
   expr ``(mul_inv_rev),
   expr ``(one_inv),
   expr ``(mul_inv_cancel_left),
   expr ``(inv_mul_cancel_left),
   expr ``(pow_one),
   expr ``(gpow_one),
   expr ``(gpow_neg),
   expr ``(pow_zero),
   expr ``(gpow_zero),
   expr ``(gpow_add),
   expr ``(pow_add),
   expr ``(gpow_bit0),
   expr ``(gpow_bit1),
   expr ``(pow_bit0),
   expr ``(pow_bit1)]
>>= λ x, return x.fst

end

meta def group_rel_m.run (red : transparency) (G : expr)
  {α} (m : group_rel_m α) : tactic α :=
do u ← mk_meta_univ,
   infer_type G >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   ic ← mk_instance_cache G,
   zc ← mk_instance_cache `(ℤ),
   fsl ← mk_free_group_simp_lemmas,
   esl ← mk_eval_simp_lemmas,
   using_new_ref ic $ λ ric,
   using_new_ref mk_buffer $ λ atoms,
   reader_t.run m ⟨G, u, red, ric, atoms, fsl, esl⟩

namespace group_rel_m

meta def lift {α : Type} : tactic α → group_rel_m α := reader_t.lift

/-- Lift an instance cache tactic (probably from `norm_num`) to the `ring_m` monad. This version
is abstract over the instance cache in question (either the ring `α`, or `ℕ` for exponents). -/
@[inline] meta def ic_lift' (icf : cache → ref instance_cache) {α}
  (f : instance_cache → tactic (instance_cache × α)) : group_rel_m α :=
⟨λ c, do
  let r := icf c,
  ic ← read_ref r,
  (ic', a) ← f ic,
  a <$ write_ref r ic'⟩

/-- Lift an instance cache tactic (probably from `norm_num`) to the `group_rel_m` monad. This uses
the instance cache corresponding to the ring `α`. -/
@[inline] meta def ic_lift {α} : (instance_cache → tactic (instance_cache × α)) → group_rel_m α :=
ic_lift' cache.ic

meta def add_atom (e : expr) : group_rel_m ℕ :=
⟨λ l, do es ← read_ref l.atoms,
  es.iterate failed (λ n e' t, t <|> (is_def_eq e e' l.red $> n.1)) <|>
    (es.size <$ write_ref l.atoms (es.push_back e))⟩

/-- Get an already encountered atom by its index. -/
meta def get_atom (n : ℕ) : group_rel_m expr :=
⟨λ c, do es ← read_ref c.atoms, pure (es.read' n)⟩

meta def to_free_group : expr → group_rel_m free_group
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

inductive proof_eq_one
  {G : Type*} [group G] (atoms : list G) :
  free_group → Prop
| one : proof_eq_one 1
| step :
  Π (word₁ rel word₂ conj old_word new_word rel_conj : free_group),
  proof_eq_one new_word →
  word₁ ++ word₂ = old_word
  → eval atoms rel = 1
  → conj⁻¹ * word₁ * rel_conj⁻¹ * rel * rel_conj * word₂ * conj = new_word
  → proof_eq_one old_word

theorem eq_one_of_proof_eq_one {G : Type*} [group G] (atoms : list G)
  (g : free_group) (h : proof_eq_one atoms g) : eval atoms g = 1 :=
begin
  induction h with word₁ rel word₂ conj old_word new_word op h₁ h₂ h₃ ih h,
  { refl },
  { substs ih h₂,
    simp only [eval_mul, h₃, one_mul, mul_assoc, eval_inv, inv_mul_cancel_left] at h,
    rw [inv_mul_eq_one, ← mul_assoc, ← mul_inv_eq_iff_eq_mul, mul_inv_self] at h,
    rw [h, eval_append] }
end

theorem helper {G : Type*} [group G] (atoms : list G) (lhs rhs : G)
  (g : free_group) (h : proof_eq_one atoms g) (hlr : eval atoms g * (rhs * lhs⁻¹) = 1) :
  lhs = rhs :=
by rwa [eq_one_of_proof_eq_one atoms g h, one_mul, mul_inv_eq_one, eq_comm] at hlr
-- forgot to conjugate relation
-- reverse list before applying
meta def make_proof_eq_one_expr
  (atoms : expr)
  (rel_eq_one : buffer expr)
  (rel_inv_eq_one : buffer expr)
  (rels : buffer free_group)
  (rels_inv : buffer free_group) :
  list path_step → group_rel_m expr
| []     := ic_lift (λ ic, ic.mk_app ``proof_eq_one.one [atoms])
| (p::l) :=
  do pr ← make_proof_eq_one_expr l,
  c ← get_cache,
  let word₁ := p.old_word.take p.word_start_index,
  let word₂ := p.old_word.drop p.word_start_index,
  let rel := cond p.rel_is_inv
    (rels.read' p.rel_index)
    (rels_inv.read' p.rel_index),
  let rel_conj := rel.take (rel.length - p.rel_letter_index),
  let conj := cyclically_reduce_conj (word₁ * rel_conj⁻¹ * rel * rel_conj * word₂),
  --proof_eq : expr × expr ← lift (simplify c.free_group_simp_lemmas []
    -- `(((%%(to_expr conj))⁻¹ * %%(to_expr word₁) *
    --   (%%(to_expr rel_conj))⁻¹ *
    --   %%(to_expr rel) *
    --   %%(to_expr rel_conj) *
    --   %%(to_expr word₂) *
    --   (%%(to_expr conj)) : free_group))),
  ic_lift (λ ic, ic.mk_app ``proof_eq_one.step
    [atoms,
     to_expr word₁,
     to_expr rel,
     to_expr word₂,
     to_expr conj,
     to_expr p.old_word,
     to_expr p.new_word,
     to_expr rel_conj,
     pr,
     `(@eq.refl free_group %%(to_expr p.old_word)),
     cond p.rel_is_inv
      (rel_eq_one.read' p.rel_index)
      (rel_inv_eq_one.read' p.rel_index),
    `(@eq.refl free_group %%(to_expr p.new_word))])

lemma mul_inv_eq_one_of_eq {G : Type*} [group G] (a b : G) (h : a = b) : a * b⁻¹ = 1 :=
by simp [h]

lemma eq_of_mul_inv_eq_one {G : Type*} [group G] (a b : G) (h : a * b⁻¹ = 1) :
  a * b⁻¹ = 1 :=
by simp [h]

meta def list_atoms : group_rel_m expr :=
do c ← get_cache,
atoms ← lift $ read_ref c.atoms,
lift $ atoms.to_list.foldr
  (λ atom l, do l ← l, mk_mapp `list.cons [some c.G, some atom, some l])
  (mk_mapp `list.nil [some c.G])
-- lemma eval_inv_eq_one_of_eval_eq_one {G : Type*} [group G]
--   (w₁ w₂ : free_group) (h : w₁⁻¹ = w₂) (l : list G) (h₂ : eval l w₁ = 1) :
--   eval l w₂ = 1 :=
-- by rw [← h, eval_inv, h₂, one_inv]

-- whilst true, it's not the right lemma. Need the hypothesis
-- that eval atoms w
lemma eval_eq_one {G : Type*} [group G] (lhs rhs : G) (h : lhs = rhs) (w : free_group)
  (atoms : list G) (hw : eval atoms w * (rhs * lhs⁻¹) = 1) : eval atoms w = 1 :=
begin
  rw [mul_eq_one_iff_eq_inv] at hw,
  rw [hw, h],
  simp
end

-- lemma eval_inv_eq_one {G : Type*} [group G] (lhs rhs : G) (h : lhs = rhs) (w : free_group)
--   (atoms : list G) (hw : eval atoms w * (rhs * lhs⁻¹) = 1) : eval atoms w = 1 :=
-- begin
--   rw [mul_eq_one_iff_eq_inv] at hw,
--   rw [hw, h],
--   simp
-- end

--make a proof that `eval atoms g * (rhs * lhs⁻¹) = whatever`
meta def make_proof_eval_eq (lhs rhs : expr)
    (g : free_group) (atoms : expr) : group_rel_m expr :=
do lhs_inv : expr ← ic_lift $ λ ic, ic.mk_app `has_inv.inv [lhs],
rhs_mul_lhs_inv : expr ← ic_lift $ λ ic, ic.mk_app `has_mul.mul [rhs, lhs_inv],
eval_g : expr ← ic_lift $ λ ic, ic.mk_app ``eval [atoms, to_expr g],
eval_g_mul : expr ← ic_lift $ λ ic, ic.mk_app `has_mul.mul [eval_g, rhs_mul_lhs_inv],
c ← get_cache,
let esl := c.eval_simp_lemmas,
proof_aux : expr × expr ← lift $ simplify esl [] eval_g_mul,
return proof_aux.2

-- make a proof that `eval atoms g = 1` given
meta def make_proof_eval_eq_one (lhs rhs : expr)
  (e : expr) --proof lhs = rhs
  (g : free_group) (atoms : expr) : group_rel_m expr :=
do proof_aux : expr ← make_proof_eval_eq lhs rhs g atoms,
ic_lift $ λ ic, ic.mk_app ``eval_eq_one
  [lhs, rhs, e, to_expr g, atoms, proof_aux]

meta def make_proofs
  (pr lhs rhs : expr)
  (lhsg rhsg : free_group) : group_rel_m (expr × expr) :=
do
atoms ← list_atoms,
c ← get_cache,
let esl := c.eval_simp_lemmas,
let rel := lhsg * rhsg⁻¹,
let rel_inv := rhsg * lhsg⁻¹,
pr_symm ← lift $ mk_eq_symm pr,
proof1 : expr ← make_proof_eval_eq_one lhs rhs pr rel atoms,
proof2 : expr ← make_proof_eval_eq_one rhs lhs pr_symm rel_inv atoms,
name1 ← lift mk_fresh_name,
name2 ← lift mk_fresh_name,
e₁ ← lift $ note name1 none proof1,--proof1,
e₂ ← lift $ note name2 none proof2,
return (e₁, e₂)

meta def mk_list_free_group : list expr → group_rel_m
  (list (expr × -- proof
    expr × expr × -- lhs rhs
    free_group × free_group))
| []                  := return []
| (e::l) :=
  do t ← lift $ infer_type e,
  match t with
  | `(%%e₁= %%e₂) :=
    do l ← mk_list_free_group l,
    lhsg ← to_free_group e₁,
    rhsg ← to_free_group e₂,
    return ((e, e₁, e₂, lhsg, rhsg)::l)
  | _ := mk_list_free_group l
  end

meta def group_rel (hyps : list expr) (tlhs : expr) (trhs : expr) : group_rel_m unit :=
do --type_hyps ← hyps.mmap (lift ∘ infer_type),
list_rels : list (expr × expr × expr × free_group × free_group) ← mk_list_free_group hyps,
  lhsg ← to_free_group tlhs,
  rhsg ← to_free_group trhs,
  p : list (expr × expr) ← list_rels.mmap
    (λ l, make_proofs l.1 l.2.1 l.2.2.1 l.2.2.2.1 l.2.2.2.2),
  let path := trace_path (solve (list_rels.map (λ l, l.2.2.2.1 * l.2.2.2.2⁻¹)) (lhsg * rhsg⁻¹)).2,
  lift $ tactic.trace ("path length = " ++ repr path.length),
  atoms ← list_atoms,
  lift $ tactic.trace atoms,
  e ← make_proof_eq_one_expr atoms
    (list.to_buffer (p.map prod.fst))
    (list.to_buffer (p.map prod.snd))
    (list.to_buffer (list_rels.map (λx, x.2.2.2.1 * x.2.2.2.2⁻¹)))
    (list.to_buffer (list_rels.map (λx, x.2.2.2.2 * x.2.2.2.1⁻¹)))
    path.reverse,
  t ← make_proof_eval_eq tlhs trhs (lhsg * rhsg⁻¹) atoms,
  pr ← ic_lift $ λ ic, ic.mk_app ``helper
    [atoms, tlhs, trhs, to_expr (lhsg * rhsg⁻¹), e, t],

  lift $ tactic.exact pr

end group_rel_m

end group_rel

namespace tactic.interactive

open interactive.types interactive tactic expr group_rel

meta def group_rel (hyps : parse (list_of texpr)) : tactic unit :=
do tgt ← target,
(lhs, rhs) ← is_eq tgt,
G ← infer_type lhs,
hyps' : list expr ← hyps.mmap i_to_expr,
group_rel_m.run (transparency.semireducible) G (group_rel_m.group_rel hyps' lhs rhs)

end tactic.interactive

set_option profiler true
