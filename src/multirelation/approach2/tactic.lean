import .approach2
import tactic.ring_exp
import tactic

namespace group_rel
open expr tactic free_group native

meta structure cache :=
(G : expr)
(univ : level)
(red : transparency)
(ic : ref instance_cache) -- instance_cache for G
(atoms : ref (buffer (expr × option (expr × expr))))
(has_pow : expr)
(free_group_simp_lemmas : simp_lemmas)
(numeral_simp_lemmas₁ : simp_lemmas)
(numeral_simp_lemmas₂ : simp_lemmas)

@[derive [monad, alternative]]
meta def group_rel_m (α : Type) : Type :=
reader_t cache tactic α

meta def get_cache : group_rel_m cache := reader_t.read

meta def lift {α : Type} : tactic α → group_rel_m α := reader_t.lift

meta instance {α : Type} : has_coe (tactic α) (group_rel_m α) := ⟨lift⟩

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

/-- make the application `n G i l`, where `i` is some instance found in the cache for `G` -/
meta def mk_app (n : name) (l : list expr) : group_rel_m expr :=
ic_lift $ λ ic, ic.mk_app n l

section ring_exp
open tactic.ring_exp

section simp_arg_type
open tactic.simp_arg_type

meta def mk_int_to_nat_simp_lemmas : tactic simp_lemmas :=
do sl ← mk_simp_set tt []
  [expr ``(int.coe_nat_one),
   expr ``(int.coe_nat_zero),
   expr ``(int.coe_nat_add),
   expr ``(int.coe_nat_pow),
   expr ``(int.coe_nat_mul),
   expr ``(int.coe_nat_bit0),
   expr ``(int.coe_nat_bit1),
   expr ``(gpow_zero),
   expr ``(gpow_one),
   symm_expr ``(gpow_coe_nat)],
return sl.1

/-- unfold all natural number multiplications -/
meta def mk_numeral_simp_lemmas₁ : tactic simp_lemmas :=
do sl ← mk_simp_set tt []
  [expr ``(@mul_comm ℤ _ (bit0 _)),
   expr ``(@mul_comm ℤ _ (bit1 _)),
   expr ``(@mul_right_comm ℤ _ _ (bit0 _)),
   expr ``(@mul_right_comm ℤ _ _ (bit1 _))],
return sl.1

meta def mk_numeral_simp_lemmas₂ : tactic simp_lemmas :=
do sl ← mk_simp_set tt []
  [expr ``(@bit0.equations._eqn_1),
   expr ``(@bit1.equations._eqn_1),
   expr ``(@mul_add),
   expr ``(@mul_one)],
return sl.1

end simp_arg_type

meta def normalize_exponent_ring_exp (e : expr) : group_rel_m (expr × expr) :=
do (e₁, pr₁) ←
  ((do info_b ← mk_const ``int >>= make_eval_info,
    info_e ← mk_const ``nat >>= make_eval_info,
    (λ x : (_ × _), x.1) <$> (state_t.run
      (reader_t.run (eval_simple e) ⟨info_b, info_e, transparency.semireducible⟩) [])) :
        tactic (expr × expr)),
  c ← get_cache,
  (e₂, pr₂) ← (simplify c.numeral_simp_lemmas₁ [] e <|> return (e₁, `(@eq.refl ℤ %%e₁))),
  (e₃, pr₃) ← (simplify c.numeral_simp_lemmas₂ [] e <|> return (e₂, `(@eq.refl ℤ %%e₂))),
  pr ← mk_eq_trans pr₁ pr₂,
  pr ← mk_eq_trans pr pr₃,
  return (e₃, pr)

end ring_exp

meta def run (red : transparency) (G : expr)
  {α} (m : group_rel_m α) : tactic α :=
do u ← mk_meta_univ,
   infer_type G >>= unify (expr.sort (level.succ u)),
   u ← get_univ_assignment u,
   ic ← mk_instance_cache G,
   zc ← mk_instance_cache `(ℤ),
   fsl ← mk_free_group_simp_lemmas,
   nsl₁ ← mk_numeral_simp_lemmas₁,
   nsl₂ ← mk_numeral_simp_lemmas₂,
   pow ← tactic.mk_app `has_pow [G, `(int)],
   has_pow ← mk_instance pow,
   using_new_ref ic $ λ ric,
   using_new_ref mk_buffer $ λ atoms,
   reader_t.run m ⟨G, u, red, ric, atoms, has_pow, fsl, nsl₁, nsl₂⟩

run_cmd run (transparency.semireducible) `(units ℤ)
  (normalize_exponent_ring_exp `((4 : ℤ))) >>= trace

meta def add_atom (e : expr × option (expr × expr)) : group_rel_m ℕ :=
⟨λ l, do es ← read_ref l.atoms,
  es.iterate failed (λ n e' t, t <|> (is_def_eq e.1 e'.1 l.red $> n.1)) <|>
    (es.size <$ write_ref l.atoms (es.push_back e))⟩

meta def prove_free_group_eqv (lhs : expr) : group_rel_m expr :=
do c ← get_cache,
free_group_simp lhs c.free_group_simp_lemmas

/-- Get an already encountered atom by its index. -/
meta def get_atom (n : ℕ) : group_rel_m (expr × option (expr × expr)) :=
⟨λ c, do es ← read_ref c.atoms, pure (es.read' n)⟩

lemma eval_mul_congr {G : Type*} [group G] (atoms : list G)
  (a b : G) (a' b' ab : free_group)
  (ha : eval atoms a' = a)
  (hb : eval atoms b' = b)
  (hab : eqv (ap a' b') ab) :
  eval atoms ab = a * b :=
by simp [← eval_eq_of_eqv atoms hab, eval_ap, *]

lemma eval_inv_congr {G : Type*} [group G] (atoms : list G)
  (a : G) (a' a_inv : free_group)
  (ha : eval atoms a' = a)
  (ha_inv : eqv (inv_core a' 1) a_inv) :
  eval atoms a_inv = a⁻¹ :=
by simp [inv_core_eq, ← eval_eq_of_eqv atoms ha_inv, eval_inv, eval_append, eval_one, *]

lemma pow_congr {G : Type*} [group G] (atoms : list G) (a : G) (n m : ℤ)
  (a' : free_group)
  (ha : eval atoms a' = a ^ m)
  (h : n = m) :
  eval atoms a' = a ^ n :=
by subst h; assumption

lemma eval_pow_add_congr {G : Type*} [group G] (atoms : list G) (a : G) (n m : ℤ)
  (an am anam : free_group)
  (han : eval atoms an = a ^ n)
  (ham : eval atoms am = a ^ m)
  (hanam : eqv (ap an am) anam) :
  eval atoms anam = a ^ (n + m) :=
sorry

lemma eval_pow_sub_congr {G : Type*} [group G] (atoms : list G) (a : G) (n m : ℤ)
  (an am anam : free_group)
  (han : eval atoms an = a ^ n)
  (ham : eval atoms an = a ^ m)
  (hanam : eqv (inv_core an am) anam) :
  eval atoms anam = a ^ (n - m) :=
sorry

lemma eval_pow_neg_congr {G : Type*} [group G] (atoms : list G) (a : G) (n : ℤ)
  (an ann : free_group)
  (han : eval atoms an = a ^ n)
  (hanam : eqv (inv_core an 1) ann) :
  eval atoms ann = a ^ (-n) :=
sorry

-- lemma eval_pow_bit0_congr {G : Type*} [group G] (atoms : list G) (a : G) (n : ℤ)
--   (an ann : free_group)
--   (han : eval atoms an = a ^ n)
--   (hanam : eqv (ap an an) ann) :
--   eval atoms ann = a ^ (bit0 n) :=
-- sorry

-- lemma eval_pow_bit1_congr {G : Type*} [group G] (atoms : list G) (a : G) (n : ℤ)
--   (a' an ann : free_group)
--   (han : eval atoms an = a ^ n)
--   (ha : eval atoms a' = a)
--   (hanam : eqv (ap a' (ap an an)) ann) :
--   eval atoms ann = a ^ (bit1 n) :=
-- sorry

lemma eval_pow_one_congr {G : Type*} [group G] (atoms : list G) (a : G)
  (a' : free_group)
  (ha : eval atoms a' = a) :
  eval atoms a' = a ^ (1 : ℤ) :=
sorry

meta def exp_to_free_group (atoms : expr) (a : expr) (a_index : ℕ) (a_pr : expr) :
  Π (n : expr), group_rel_m (free_group × expr)
| `(%%n + %%m) :=
do
  (an', pr₁) ← exp_to_free_group n,
  (am', pr₂) ← exp_to_free_group m,
  let anam' := an' * am',
  pr_eqv ← prove_free_group_eqv `(ap %%(to_expr an') %%(to_expr am')),
  pr ← mk_app ``eval_pow_add_congr
    [atoms, a, n, m, to_expr an', to_expr am',
      to_expr anam', pr₁, pr₂, pr_eqv],
  return (anam', pr)
| `(%%n - %%m) :=
do
  (an', pr₁) ← exp_to_free_group n,
  (am', pr₂) ← exp_to_free_group m,
  let anam' := an' * am',
  pr_eqv ← prove_free_group_eqv `(inv_core %%(to_expr an') %%(to_expr am')),
  pr ← mk_app ``eval_pow_sub_congr
    [atoms, a, n, m, to_expr an', to_expr am',
      to_expr anam', pr₁, pr₂, pr_eqv],
  return (anam', pr)
| `(-%%n) :=
do
  (an', pr₁) ← exp_to_free_group n,
  let anam' := an'⁻¹,
  pr_eqv ← prove_free_group_eqv `(inv_core %%(to_expr an') 1),
  pr ← mk_app ``eval_pow_neg_congr
    [atoms, a, n, to_expr an', to_expr anam', pr₁, pr_eqv],
  return (anam', pr)
-- | `(bit0 %%n) :=
-- do
--   (an', pr₁) ← exp_to_free_group n,
--   let anam' := an' * an',
--   pr_eqv ← prove_free_group_eqv `(ap an' an'),
--   pr ← mk_app ``eval_pow_bit0_congr
--     [atoms, a, n, to_expr an', to_expr anam', pr₁, pr_eqv],
--   return (anam', pr)
-- | `(bit1 %%n) :=
-- do
--   (an', pr₁) ← exp_to_free_group n,
--   let ann' : free_group := [⟨a_index, ff⟩] * an' * an',
--   pr_eqv ← prove_free_group_eqv `(ap %%a (ap %%(to_expr an') %%(to_expr an'))),
--   pr ← mk_app ``eval_pow_bit1_congr
--     [atoms, a, n, to_expr [⟨a_index, ff⟩], to_expr an', to_expr ann', pr₁, pr_eqv],
--   return (ann', pr)
| `((1 : ℤ)) :=
  do pr ← mk_app ``eval_pow_one_congr [atoms, a, to_expr [⟨a_index, ff⟩], a_pr],
  return ([⟨a_index, ff⟩], pr)
| n :=
do c ← get_cache,
  let e : expr :=
    expr.app (expr.app (expr.app (expr.app (expr.app (expr.const `has_pow.pow
      [c.univ, level.zero]) c.G) (expr.const `int [])) c.has_pow) a) n,
  i ← add_atom (e, some (a, n)),
  pr ← mk_app `mul_one [e],
  return ([⟨i, ff⟩], pr)

meta def to_free_group (atoms : expr) :
  expr → group_rel_m (free_group × expr)
| `(%%a * %%b) :=
  do (a', pra) ← to_free_group a,
     (b', prb) ← to_free_group b,
     let ab' := a' * b',
     fpr ← prove_free_group_eqv `(ap %%(to_expr a') %%(to_expr b')),
     pr ← mk_app ``eval_mul_congr
       [atoms,
        a, b,
        to_expr a', to_expr b',
        to_expr ab',
        pra, prb,
        fpr],
     return (a' * b', pr)
| `((%%a)⁻¹) :=
  do (a', pr) ← to_free_group a,
  let a'_inv := a'⁻¹,
  fpr ← prove_free_group_eqv `(inv_core %%(to_expr a') 1),
  pr ← mk_app ``eval_inv_congr
    [atoms, a, to_expr a', to_expr a'_inv, pr, fpr],
  return (a'_inv, pr)
| `(@has_one.one _ _) :=
  do pr ← mk_app ``eval_one [atoms],
  return (1, pr)
| `(%%a ^ (%%n)) :=
  do (n', pr₁) ← normalize_exponent_ring_exp n,
    i ← add_atom (a, none),
    pr ← mk_app ``mul_one [a],
    (w, pr₂) ← exp_to_free_group atoms a i pr n',
    pr ← mk_app ``pow_congr
      [atoms, a, n, n', to_expr w, pr₂, pr₁],
    return (w, pr)
| e := do i ← add_atom (e, none),
  pr ← mk_app `mul_one [e],
  return (of i, pr)

local infix `*'`:70 := ap
local infixl `≡` :50 := free_group.eqv

inductive proof_eq_one
  {G : Type*} [group G] (atoms : list G) :
  free_group → Prop
| one : proof_eq_one 1
| step :
  Π (word₁ rel word₂ conj old_word new_word rel_conj : free_group),
  proof_eq_one new_word →
  (word₁ *' word₂) ≡ old_word
  → eval atoms rel = 1
  → inv_core conj word₁ *' inv_core rel_conj rel *' rel_conj *' word₂ *' conj ≡ new_word
  → proof_eq_one old_word

theorem eq_of_eval_eq_one {G : Type*} [group G] (atoms : list G)
  (lhs rhs : G) (w : free_group) (h : eval atoms w = lhs * rhs⁻¹)
  (h₂ : eval atoms w = 1) : lhs = rhs :=
mul_inv_eq_one.1 (h ▸ h₂)

theorem eq_one_of_proof_eq_one {G : Type*} [group G] (atoms : list G)
  (g : free_group) (h : proof_eq_one atoms g) : eval atoms g = 1 :=
begin
  induction h with word₁ rel word₂ conj old_word new_word op h₁ h₂ h₃ ih h,
  { refl },
  { rw [← eval_eq_of_eqv atoms ih] at h,
    simp only [eval_ap, h₃, one_mul, mul_assoc, eval_inv, inv_mul_cancel_left,
      inv_core_eq, eval_append] at h,
    rw [inv_mul_eq_one, ← mul_assoc, ← mul_inv_eq_iff_eq_mul, mul_inv_self] at h,
    rw [← eval_eq_of_eqv atoms h₂, eval_ap, ← h] }
end

-- reverse list before applying
meta def make_proof_eq_one_expr
  (atoms : expr)
  (rel_eq_one : buffer expr)
  (rel_inv_eq_one : buffer expr)
  (rels : buffer free_group)
  (rels_inv : buffer free_group) :
  list path_step → group_rel_m expr
| []     := mk_app ``proof_eq_one.one [atoms]
| (p::l) :=
  do pr ← make_proof_eq_one_expr l,
  c ← get_cache,
  let word₁ := p.old_word.take p.word_start_index,
  let word₂ := p.old_word.drop p.word_start_index,
  let rel := cond p.rel_is_inv
    (rels.read' p.rel_index)
    (rels_inv.read' p.rel_index),
  let rel_conj := rel.take
    (let x := rel.length - p.rel_letter_index in if x = rel.length then 0 else x),
  let conj := cyclically_reduce_conj (word₁ * rel_conj⁻¹ * rel * rel_conj * word₂),
  proof_rel₁ : expr ← prove_free_group_eqv `(%%(to_expr word₁) *' %%(to_expr word₂)),
  proof_rel₂ : expr ← prove_free_group_eqv
    `(inv_core %%(to_expr conj) %%(to_expr word₁) *' inv_core
        %%(to_expr rel_conj) %%(to_expr rel) *' %%(to_expr rel_conj) *'
        %%(to_expr word₂) *' %%(to_expr conj)),
  mk_app ``proof_eq_one.step
    [atoms,
     to_expr word₁,
     to_expr rel,
     to_expr word₂,
     to_expr conj,
     to_expr p.old_word,
     to_expr p.new_word,
     to_expr rel_conj,
     pr,
     proof_rel₁,
     cond p.rel_is_inv
      (rel_eq_one.read' p.rel_index)
      (rel_inv_eq_one.read' p.rel_index),
    proof_rel₂]

meta def get_atoms : group_rel_m (buffer (expr × option (expr × expr))) :=
do c ← get_cache, read_ref c.atoms

meta def list_atoms : group_rel_m expr :=
do c ← get_cache,
atoms ← read_ref c.atoms,
atoms.to_list.foldr
  (λ atom l, do l ← l, mk_mapp `list.cons [some c.G, some atom.1, some l])
  (mk_mapp `list.nil [some c.G])

lemma eval_eq_one₂ {G : Type*} [group G] (atoms : list G)
  (lhs rhs : G) (h : lhs = rhs) (lhsg rhsg lr : free_group)
  (hlhs : eval atoms lhsg = lhs)
  (hrhs : eval atoms rhsg = rhs)
  (heq : lr = lhsg * rhsg⁻¹) : eval atoms lr = 1 :=
begin
  substs lr lhs,
  simp [hrhs, eval_mul, eval_inv, hlhs]
end

lemma eq_of_eval_eq_one₂ {G : Type*} [group G] (atoms : list G)
  (lhs rhs : G) (lhsg rhsg lr : free_group)
  (hlhs : eval atoms lhsg = lhs)
  (hrhs : eval atoms rhsg = rhs)
  (heqv : lr *' rhsg ≡ lhsg)
  (hlr : eval atoms lr = 1) :
  lhs = rhs  :=
by simpa [← eval_eq_of_eqv atoms heqv, hrhs, eval_ap, eval_inv, inv, mul_inv_eq_one, ← hlhs] using hlr

lemma eval_conj_eq_one {G : Type*} [group G] (atoms : list G)
  (rel conj new_rel : free_group) (h : inv_core conj rel *' conj ≡ new_rel)
  (rel_eq_one : eval atoms rel = 1) :
  eval atoms new_rel = 1 :=
by simp [← eval_eq_of_eqv atoms h, inv_core_eq, rel_eq_one, eval_inv, eval_append, eval_ap, inv]

meta def cyclically_reduce_rel (atoms : expr) (rel : free_group) (rel_eq_one : expr) :
  group_rel_m (free_group × expr) :=
let a : free_group := cyclically_reduce_conj rel in
if a = 1
  then return (rel, rel_eq_one)
  else do
    let new_rel := a⁻¹ * rel * a,
    pr_eqv ← prove_free_group_eqv `(inv_core %%(to_expr a) %%(to_expr rel) *' %%(to_expr a)),
    pr ← mk_app ``eval_conj_eq_one
      [atoms, to_expr rel, to_expr a, to_expr new_rel, pr_eqv, rel_eq_one],
    return (new_rel, pr)

lemma eval_inv_eq_one {G : Type*} [group G] (atoms : list G) (rel rel_inv : free_group)
  (h : eqv (inv_core rel []) rel_inv) (hrel : eval atoms rel = 1) : eval atoms rel_inv = 1 :=
by rw [← eval_eq_of_eqv atoms h, inv_core_eq, eval_append, eval, mul_one, eval_inv, hrel, one_inv]

meta def make_proof_inv_eq_one (atoms : expr)
  (rel : free_group) (rel_eq_one : expr) :
  group_rel_m (free_group × expr) :=
do
let rel_inv := rel⁻¹,
pr_eqv ← prove_free_group_eqv `(inv_core %%(to_expr rel) 1),
pr ← mk_app ``eval_inv_eq_one
  [atoms, to_expr rel, to_expr rel_inv,
    pr_eqv,
    rel_eq_one],
return (rel_inv, pr)

meta def make_proof' (atoms : expr) (hyp_type hyp_pr : expr) :
  group_rel_m (free_group × free_group × expr × expr) :=
do
  (lhs, rhs) ← is_eq hyp_type,
  (lhsg, prl) ← to_free_group atoms lhs,
  (rhsg, prr) ← to_free_group atoms rhs,
  let lr := lhsg * rhsg⁻¹,
  pr ← mk_app ``eval_eq_one₂
    [atoms, lhs, rhs, hyp_pr, to_expr lhsg, to_expr rhsg, to_expr lr,
    prl, prr, `(@eq.refl free_group %%(to_expr lr))],
  (lr, pr) ← cyclically_reduce_rel atoms lr pr,
  (lr_inv, pr_inv) ← make_proof_inv_eq_one atoms lr pr,
  return (lr, lr_inv, pr, pr_inv)

section subst

meta def subst_into_rel (rel word : free_group)
  (i : ℕ) (r₁ r₂ : free_group)
  (rel_eq_one  word_eq_one : expr) :
  group_rel_m (free_group × expr) :=
do atoms ← list_atoms,
let new_word := free_group.subst i (r₁⁻¹ * r₂⁻¹) word,
pr ← mk_app ``subst_eq_one_of_eq_one
  [atoms, reflect i, to_expr r₁, to_expr r₂, to_expr rel,
    to_expr (r₁⁻¹ * r₂⁻¹),
    to_expr word, to_expr new_word,
    `(@eq.refl free_group (%%(to_expr (r₁⁻¹ * r₂⁻¹)))),
    `(@eq.refl free_group %%(to_expr rel)),
    rel_eq_one,
    word_eq_one,
    `(@eq.refl free_group %%(to_expr new_word))],
cyclically_reduce_rel atoms new_word pr

meta def subst_into_target (rel word : free_group)
  (i : ℕ) (r₁ r₂ : free_group)
  (rel_eq_one : expr) :
  group_rel_m free_group :=
do atoms ← list_atoms,
let new_word := free_group.subst i (r₁⁻¹ * r₂⁻¹) word,
pr ← mk_app ``eq_one_of_subst_eq_one
  [atoms, reflect i, to_expr r₁, to_expr r₂, to_expr rel,
    to_expr (r₁⁻¹ * r₂⁻¹),
    to_expr word,
    to_expr new_word,
    `(@eq.refl free_group (%%(to_expr (r₁⁻¹ * r₂⁻¹)))),
    `(@eq.refl free_group %%(to_expr rel)),
    rel_eq_one,
    `(@eq.refl free_group new_word)],
tactic.apply pr { md := transparency.none },
return new_word

meta def perform_substs_core (atoms : expr) :
  Π (p₁ p₂ : list (free_group × free_group × expr × expr))
  (tgt : free_group),
  group_rel_m (list (free_group × free_group × expr × expr) × free_group)
| [] p₂ tgt := return (p₂, tgt)
| ((A@(rel, rel_inv, rel_eq_one, rel_inv_eq_one))::p₁) p₂ tgt :=
  match is_subst rel with
  | none := perform_substs_core p₁ (A :: p₂) tgt
  | (some (i, b, r₁, r₂)) :=
    do let p' := p₁ ++ p₂,
    let rel' := cond b rel_inv rel,
    let rel'_eq_one := cond b rel_inv_eq_one rel_eq_one,
    let (r₁, r₂) := cond b (r₂⁻¹, r₁⁻¹) (r₁, r₂),
    new_p : list (free_group × free_group × expr × expr) ← (p₁ ++ p₂).mmap
      (λ ⟨word, word_inv, word_eq_one, word_inv_eq_one⟩,
        show group_rel_m (free_group × free_group × expr × expr),
        from do (new_word, new_word_eq_one) ←
            subst_into_rel rel' word  i r₁ r₂ rel'_eq_one word_eq_one,
          (new_word_inv, new_word_inv_eq_one) ← make_proof_inv_eq_one atoms new_word new_word_eq_one,
          return (new_word, new_word_inv, new_word_eq_one, new_word_inv_eq_one)),
    new_tgt ← subst_into_target rel' tgt i r₁ r₂ rel'_eq_one,
    perform_substs_core new_p [] new_tgt
  end

meta def perform_substs (atoms : expr) (p : list (free_group × free_group × expr × expr)) (tgt : free_group) :
  group_rel_m (list (free_group × free_group × expr × expr) × free_group) :=
perform_substs_core atoms p [] tgt

end subst

-- meta def collect_like_exponents : group_rel_m
--   (rb_map expr-- exponee
--   (list
--   (expr × --exponent and exponee
--     option expr --exponent
--     × ℕ -- index in buffer of atoms
--     ))) :=
-- do c ← get_cache,
--   atoms ← read_ref c.atoms,
--   atoms.iterate
--     (return mk_rb_map)
--     (λ i atom m,
--       do rb ← m,
--         match atom with
--         | A@`((%%a)^(%%n)) :=
--           let e : tactic (rb_map expr (list (expr × option expr × ℕ))) :=
--             rb.fold failure (λ e l t, t <|> is_def_eq e a >>
--               return (rb.insert e ((A, some n, i)::l))) in
--           e <|> return (rb.insert a [(A, some n, i)])
--         | `(%%a) := let e : tactic (rb_map expr (list (expr × option expr × ℕ))) :=
--             rb.fold failure (λ e l t, t <|> is_def_eq e a >>
--               return (rb.insert e ((a, none, i)::l))) in
--             e <|> return (rb.insert a [(a, none, i)])
--         end).

lemma eval_gpow_gpow_comm {G : Type*} [group G] (atoms : list G) (i j : ℕ)
  (g : G) (m n : ℤ) (hi : nth atoms i = g ^ m) (hj : nth atoms j = g ^ n) :
  eval atoms [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩] = 1 :=
begin
  simp only [eval, hi, hj, ← gpow_neg, mul_one, ← gpow_add],
  rw [add_left_comm, add_neg_cancel_left, add_neg_self, gpow_zero]
end

lemma eval_gpow_comm {G : Type*} [group G] (atoms : list G) (i j : ℕ)
  (g : G) (m : ℤ) (hi : nth atoms i = g ^ m) (hj : nth atoms j = g) :
  eval atoms [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩] = 1 :=
eval_gpow_gpow_comm atoms i j g m 1 hi (by simpa)

/-- `a` -/
meta def make_pow_comm_proof (atoms : expr) (a : expr) (l : list (expr × (option expr) × ℕ)) :
  group_rel_m (list (free_group × free_group × expr × expr)) :=
do
l.mfoldl
  (λ prs₁ e₁,
    l.mfoldl
      (λ prs₂ e₂,
        if e₁.2.2 ≤ e₂.2.2
          then return prs₂
          else
            match e₁, e₂ with
            | (an₁, some n₁, i), (an₂, some n₂, j) :=
              do
                peq₁ ← mk_eq_refl an₁,
                peq₂ ← mk_eq_refl an₂,
                pr ← mk_app ``eval_gpow_gpow_comm
                  [atoms, reflect i, reflect j, a, n₁, n₂, peq₁, peq₂],
                pr ← note_anon none pr,
                let rel : free_group := [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩],
                (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
                return((rel, rel_inv, pr, pr_inv) :: prs₂)
            | (an₁, some n₁, i), (an₂, none, j) :=
               do
                peq₁ ← mk_eq_refl an₁,
                peq₂ ← mk_eq_refl an₂,
                pr ← mk_app ``eval_gpow_comm
                  [atoms, reflect i, reflect j, a, n₁, peq₁, peq₂],
                pr ← note_anon none pr,
                let rel : free_group := [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩],
                (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
                return ((rel, rel_inv, pr, pr_inv) :: prs₂)
            | (an₁, none, i), (an₂, some n₂, j) :=
              do
                peq₁ ← mk_eq_refl an₁,
                peq₂ ← mk_eq_refl an₂,
                pr ← mk_app ``eval_gpow_comm
                  [atoms, reflect j, reflect i, a, n₂, peq₂, peq₁],
                pr ← note_anon none pr,
                let rel : free_group := [⟨j, ff⟩, ⟨i, ff⟩, ⟨j, tt⟩, ⟨i, tt⟩],
                (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
                return ((rel, rel_inv, pr, pr_inv) :: prs₂)
            | _, _ := return prs₂
            end)
      prs₁)
  []

meta def make_pow_comm_proofs (atoms : expr) :
  Π (atomsl : list (expr × option (expr × expr) × ℕ)),
  group_rel_m (list (free_group × free_group × expr × expr))
| [] := return []
| ((an₁, some (a₁, n₁), i) :: l) :=
do prs ← make_pow_comm_proofs l,
  l.mfoldl
  (λ prs e,
    match e with
    | (a, none, j) := (do
      is_def_eq a a₁,
      peq₁ ← mk_eq_refl an₁,
      peq₂ ← mk_eq_refl a,
      pr ← mk_app ``eval_gpow_comm
        [atoms, reflect i, reflect j, a, n₁, peq₁, peq₂],
      pr ← note_anon none pr,
      let rel : free_group := [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩],
      (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
      return ((rel, rel_inv, pr, pr_inv) :: prs)) <|> return prs
    | (an₂, some (a₂, n₂), j) := (do
      is_def_eq a₁ a₂,
      peq₁ ← mk_eq_refl an₁,
      peq₂ ← mk_eq_refl an₂,
      pr ← mk_app ``eval_gpow_gpow_comm
        [atoms, reflect i, reflect j, a₁, n₁, n₂, peq₁, peq₂],
      pr ← note_anon none pr,
      let rel : free_group := [⟨i, ff⟩, ⟨j, ff⟩, ⟨i, tt⟩, ⟨j, tt⟩],
      (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
      return ((rel, rel_inv, pr, pr_inv) :: prs)) <|> return prs
    end)
  prs
| ((a, none, i) :: l) :=
do prs ← make_pow_comm_proofs l,
  l.mfoldl
  (λ prs e,
    match e with
    | (an₂, none, j) := return prs
    | (an₂, some (a₂, n₂), j) := (do
      is_def_eq a a₂,
      peq₁ ← mk_eq_refl a,
      peq₂ ← mk_eq_refl an₂,
      pr ← mk_app ``eval_gpow_comm
        [atoms, reflect j, reflect i, a, n₂, peq₂, peq₁],
      pr ← note_anon none pr,
      let rel : free_group := [⟨j, ff⟩, ⟨i, ff⟩, ⟨j, tt⟩, ⟨i, tt⟩],
      (rel_inv, pr_inv) ← make_proof_inv_eq_one atoms rel pr,
      return ((rel, rel_inv, pr, pr_inv) :: prs)) <|> return prs
    end)
  prs

meta def simp_rel (sl : simp_lemmas) (pr : expr) : tactic (expr × expr) :=
do t ← infer_type pr,
(do (t, pr') ← simplify sl [] t,
new_pr ← mk_eq_mp pr' pr, trace t,
return (t, new_pr)) <|> return (t, pr)

meta def group_rel_aux (isl : simp_lemmas) (hyps : list expr) (tlhs : expr) (trhs : expr) :
  group_rel_m unit :=
do
  c ← get_cache,
  list_G ← tactic.mk_app `list [c.G],
  atoms' ← mk_meta_var list_G,
  hyps' ← lift $ hyps.mmap (simp_rel isl),
  hyps₂ ← hyps'.mmap (λ a, make_proof' atoms' a.1 a.2),
  (lhsg, prl) ← to_free_group atoms' tlhs,
  (rhsg, prr) ← to_free_group atoms' trhs,
  atoms ← list_atoms,
  unify atoms' atoms,
  batoms ← get_atoms,
  pow_comm_proofs ← make_pow_comm_proofs atoms
    (batoms.iterate [] (λ i x l, (x.1, x.2, i.1) :: l)),
  a ← get_atoms,
  let tgt := lhsg * rhsg⁻¹,
  pr_eqv ← prove_free_group_eqv `(%%(to_expr tgt) *' %%(to_expr rhsg)),
  eq_of_eval_eq_one ← mk_app ``eq_of_eval_eq_one₂
    [atoms, tlhs, trhs, to_expr lhsg, to_expr rhsg, to_expr tgt, prl, prr,
      pr_eqv],
  tactic.apply eq_of_eval_eq_one,
  (new_p, tgt) ← perform_substs atoms (hyps₂ ++ pow_comm_proofs) tgt,
  trace (pow_comm_proofs.map prod.fst),
  solution ← solve (new_p.map prod.fst) tgt a.size.succ,
  let path := trace_path solution.2,
  tactic.trace ("path length = " ++ repr path.length),
  tactic.trace atoms,
  e ← make_proof_eq_one_expr atoms
    (list.to_buffer (new_p.map (λ x, x.2.2.1)))
    (list.to_buffer (new_p.map (λ x, x.2.2.2)))
    (list.to_buffer (new_p.map (λx, x.1)))
    (list.to_buffer (new_p.map (λx, x.2.1)))
    path.reverse,
  pr ← mk_app ``eq_one_of_proof_eq_one [atoms, to_expr tgt, e],
  tactic.exact pr

end group_rel

namespace tactic.interactive

open interactive.types interactive tactic expr group_rel

meta def group_rel (hyps : parse pexpr_list) : tactic unit :=
do isl ← mk_int_to_nat_simp_lemmas,
 tactic.try (simp_target isl []),
tgt ← target,
(lhs, rhs) ← is_eq tgt,
G ← infer_type lhs,
hyps' : list expr ← hyps.mmap i_to_expr,
run transparency.semireducible G (group_rel_aux isl hyps' lhs rhs)

end tactic.interactive

set_option profiler true
