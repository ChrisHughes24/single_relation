import algebra.group
import data.list.basic

@[reducible] def free_group := list (ℕ × bool)

namespace group_rel
namespace free_group
open native

def ap : free_group → free_group → free_group := (++)
def cons (i : ℕ) (b : bool) (a : free_group) : free_group :=
⟨i, b⟩ :: a

instance : has_one (free_group) := ⟨[]⟩

lemma one_def : (1 : free_group) = [] := rfl

meta def to_expr : free_group → expr
| []          := `((1 : free_group))
| (⟨i, b⟩::l) := `(cons %%(reflect i) %%(reflect b) %%(to_expr l))

-- inv_core a b is a⁻¹ * b
def inv_core : free_group → free_group → free_group
| []            l  := l
| (⟨i, n⟩::l₁)  l₂ := inv_core l₁ (⟨i, bnot n⟩::l₂)

instance : has_inv free_group := ⟨λ a, inv_core a []⟩

def inv (a : free_group) : free_group := a⁻¹

lemma inv_def (w : free_group) : w⁻¹ = inv_core w [] := rfl

def mul_aux : Π (l₁ l₂ : free_group), free_group
| []      l₂      := l₂
| (i::l₁) []      := (i :: l₁).reverse_core []
| a@(i::l₁) b@(j::l₂) :=
  if i.1 = j.1 ∧ i.2 ≠ j.2
    then mul_aux l₁ l₂
    else a.reverse_core b

instance : has_mul free_group := ⟨λ l₁ l₂, mul_aux l₁.reverse l₂⟩

lemma mul_def (w₁ w₂ : free_group) : w₁ * w₂ = mul_aux (w₁.reverse_core []) w₂ := rfl

lemma zero_eq_succ_eq (n : ℕ) : 0 = n.succ = false :=
eq_false_intro $ λ h, nat.no_confusion h

lemma succ_eq_zero_eq (n : ℕ) : n.succ = 0 = false :=
eq_false_intro $ λ h, nat.no_confusion h

example : ([⟨1, tt⟩, ⟨0, tt⟩] : free_group)⁻¹ * [⟨1, tt⟩] * [⟨2, tt⟩] *
  [⟨3, tt⟩] = [⟨0, ff⟩, ⟨2, tt⟩, ⟨3, tt⟩]  :=
begin
  simp only [inv_core, inv_def, bool.bnot_true, bool.bnot_false, eq_self_iff_true,
    true_and, and_true, one_def, mul_def, list.reverse_core, mul_aux, ne.def,
    not_false_iff, if_true, if_false, false_and, and_false,
    nat.succ.inj_eq, zero_eq_succ_eq, succ_eq_zero_eq],
end

def length (w : free_group) : ℕ := list.length w

def cost (no_atoms : ℕ) (w : free_group) : ℕ :=
w.foldl (λ cost i, cost * no_atoms + i.1.succ) 0

def subst (x : ℕ) (r : free_group) : Π (w : free_group), free_group
| [] := []
| (⟨a, b⟩::w) :=
  if a = x
    then cond b
      (r⁻¹ * subst w)
      (r * subst w)
    else [⟨a, b⟩] * subst w

section

variables {G : Type*} [group G]

def nth : list G → ℕ → G
| []     _     := 1
| (g::l) 0     := g
| (g::l) (i+1) := nth l i

def eval (l : list G) : free_group → G
| []           := 1
| (⟨i, tt⟩::w) := (nth l i)⁻¹ * eval w
| (⟨i, ff⟩::w) := (nth l i)   * eval w

lemma eval_one (l : list G) : eval l 1 = 1 := rfl

lemma eval_append (l : list G) : Π (w₁ w₂ : free_group),
  eval l (w₁ ++ w₂) = eval l w₁ * eval l w₂
| []           w₂ := by simp [eval]
| (⟨i, tt⟩::w) w₂ := by simp [*, eval, mul_assoc]
| (⟨i, ff⟩::w) w₂ := by simp [*, eval, mul_assoc]

lemma eval_cons (l : list G) (i : ℕ) (o : bool) (w : free_group) :
  eval l (cons i o w) = nth l i ^ cond o (-1 : int) (1 : int) * eval l w :=
by cases o; simp [cons, eval]

lemma eval_ap (l : list G) (w₁ w₂ : free_group) :
  eval l (ap w₁ w₂) = eval l w₁ * eval l w₂ :=
eval_append l w₁ w₂

lemma eval_mul_aux (l : list G) : ∀ w₁ w₂ : free_group,
  eval l (mul_aux w₁ w₂) = eval l (w₁.reverse_core w₂)
| []      l₂      := by simp [mul_aux, eval, list.reverse_core_eq]
| (i::l₁) []      := by simp [mul_aux, eval, list.reverse_core_eq]
| (⟨i₁, b₁⟩::w₁) (⟨i₂, b₂⟩::w₂) :=
begin
  rw [mul_aux, list.reverse_core, list.reverse_core_eq, eval_append],
  split_ifs,
  { dsimp at h,
    cases h with hi hb,
    subst hi,
    cases b₂,
    { simp [bool.eq_tt_of_ne_ff hb, eval, eval_mul_aux, list.reverse_core_eq,
        eval_append] },
    { simp [bool.eq_ff_of_ne_tt hb, eval, eval_mul_aux, list.reverse_core_eq,
        eval_append] } },
  { simp [eval_append, eval] }
end

lemma eval_mul (l : list G) (w₁ w₂ : free_group) :
  eval l (w₁ * w₂) = eval l w₁ * eval l w₂ :=
by simp [mul_def, eval_mul_aux, list.reverse_core_eq, eval_append]

lemma eval_inv_core (l : list G) : ∀ (w₁ w₂ : free_group),
  eval l (inv_core w₁ w₂) = (eval l w₁)⁻¹ * eval l w₂
| [] w             := by simp [inv_core, eval]
| (⟨i, ff⟩::w₁) w₂ :=
  by rw [inv_core, bool.bnot_false, eval_inv_core, eval,
    eval, mul_inv_rev, mul_assoc]
| (⟨i, tt⟩::w₁) w₂ :=
   by rw [inv_core, bool.bnot_true, eval_inv_core, eval,
    eval, mul_inv_rev, mul_assoc, inv_inv]

lemma eval_inv (l : list G) (w : free_group) : eval l w⁻¹ = (eval l w)⁻¹ :=
by rw [inv_def, eval_inv_core, eval, mul_one]

lemma eval_subst (l : list G) (x : ℕ) (r w : free_group)
  (h : eval l [⟨x, ff⟩] = eval l r) :
  eval l (subst x r w) = eval l w :=
begin
  induction w with i w ih,
  { refl },
  { cases i,
    rw [subst],
    split_ifs,
    { subst h_1,
      cases i_snd;
      simp [eval_mul, eval, *, eval_inv] at * },
    { cases i_snd;
      simp [eval_mul, eval, ih] } }
end

lemma subst_eq_one_of_eq_one
  (l : list G) (x : ℕ)
  (r₁ r₂ r rhs word new_word : free_group)
  (hnew_r : rhs = r₁⁻¹ * r₂⁻¹)
  (hr : r = r₁ ++ [⟨x, ff⟩] ++ r₂)
  (hr : eval l r = 1)
  (hw : eval l word = 1)
  (hs : new_word = subst x rhs word) :
  eval l new_word = 1 :=
begin
  substs rhs r new_word,
  rw [eval_subst _ _ _ _ _, hw],
  simpa [eval_mul, eval_append, eval, mul_assoc, eval_inv,
    eq_inv_mul_iff_mul_eq, eq_inv_iff_mul_eq_one] using hr
end

lemma eq_one_of_subst_eq_one
  (l : list G) (x : ℕ)
  (r₁ r₂ r rhs word new_word : free_group)
  (hnew_r : rhs = r₁⁻¹ * r₂⁻¹)
  (hr : r = r₁ ++ [⟨x, ff⟩] ++ r₂)
  (hr : eval l r = 1)
  (hs : new_word = subst x rhs word)
  (hw : eval l new_word = 1) :
  eval l word = 1 :=
begin
  substs rhs r new_word,
  rw [eval_subst] at hw, rw hw,
  { simp only [eval_append, eval_mul, eval_inv] at *,
    rwa [eq_inv_mul_iff_mul_eq, eq_inv_iff_mul_eq_one] }
end

meta def is_subst_aux : free_group → free_group →
  rb_set ℕ →
  rb_map ℕ (ℕ × bool × free_group × free_group) →
  rb_set ℕ × rb_map ℕ (ℕ × bool × free_group × free_group)
| []     []          rbs rbm := (rbs, rbm)
| (a::l) []          rbs rbm := is_subst_aux l [a] (rbs.insert a.1) (rbm.insert a.1 (a.1, a.2, [], l))
| (a::l₁) w₂@(b::l₂) rbs rbm :=
  match rbs.contains a.1 with
  | ff := is_subst_aux l₁ (a::b::l₂) (rbs.insert a.1) (rbm.insert a.1 (a.1, a.2, w₂.reverse, l₁))
  | tt := is_subst_aux l₁ (a::b::l₂) rbs (rbm.erase a.1)
  end
| [] l₂ rbs rbm := (rbs, rbm)
end

/-- is_subst `w` returns `(i, b, w₁, w₂)` such that `w = w₁ ++ [⟨i, b⟩] ++ w₂`,
  and neither `w₁` nor `w₂` contain `i` -/
meta def is_subst (w : free_group) : option (ℕ × bool × free_group × free_group) :=
(is_subst_aux w [] mk_rb_map mk_rb_map).2.min

meta def cyclically_reduce_aux : Π (w wr : free_group), free_group
| [] wr := []
| w []  := []
| w@(⟨i₁, b₁⟩::l₁) (⟨i₂, b₂⟩::l₂) :=
  if i₁ = i₂ ∧ b₁ = bnot b₂
    then cyclically_reduce_aux l₁.init l₂.init
    else w

meta def cyclically_reduce (w : free_group) : free_group :=
cyclically_reduce_aux w w.reverse

meta def cyclically_reduce_conj_aux : Π (w wr : free_group), free_group
| [] wr := []
| w []  := []
| w@(⟨i₁, b₁⟩::l₁) (⟨i₂, b₂⟩::l₂) :=
  if i₁ = i₂ ∧ b₁ = bnot b₂
    then [⟨i₁, b₁⟩] ++ cyclically_reduce_conj_aux l₁.init l₂.init
    else 1

/-- if `c = cyclically_reduce_conj w` then `c⁻¹ * w * c` is cyclically reduced-/
meta def cyclically_reduce_conj (w : free_group) : free_group :=
cyclically_reduce_conj_aux w w.reverse

def of : ℕ → free_group := λ n, [(n, ff)]

def lt : Π (a b : free_group), bool
| _       []     := ff
| []      (a::l) := tt
| (a::l₁) (b::l₂) :=
  if a < b
    then tt
    else lt l₁ l₂

instance : has_pow free_group ℕ := ⟨λ a n, nat.rec_on n 1 (λ _, (* a))⟩
instance : has_pow free_group ℤ := ⟨λ a n, int.cases_on n
  ((^) a)
  (λ n, a⁻¹ ^ (n + 1))⟩

-- @[instance, priority 100000] def free_group.has_lt :
--   has_lt (free_group) := ⟨λ a b, lt a b⟩

-- instance : decidable_rel ((<) : free_group → free_group → Prop) :=
-- λ _ _, show decidable ((_ : bool) : Prop), by apply_instance

inductive certificate {G : Type*} [group G] (atoms : list G) : Type
| one : certificate
| step (conj : free_group) (rel : free_group) (hrel : eval atoms rel = 1)
  (old : certificate) : certificate

open certificate

local infix `*'`:70 := ap

def certificate.eval {G : Type*} [group G] (atoms : list G) : certificate atoms → free_group
| one := 1
| (step conj rel h old) := conj *' rel *' certificate.eval old *' inv_core conj 1

section eqv

inductive eqv : free_group → free_group → Prop
| refl : ∀ a, eqv a a
| symm : ∀ {a b}, eqv a b → eqv b a
| trans : ∀ {a b c}, eqv a b → eqv b c → eqv a c
| cons : ∀ {a b i o}, eqv a b → eqv (cons i o a) (cons i o b)
| ap : ∀ {a b c d}, eqv a b → eqv c d → eqv (ap a c) (ap b d)
| inv_core :  ∀ {a b c d}, eqv a b → eqv c d → eqv (inv_core a c) (inv_core b d)
| mul_inv_cancel : ∀ i a, eqv (cons i ff (cons i tt a)) a
| inv_mul_cancel : ∀ i a, eqv (cons i tt (cons i ff a)) a

attribute [refl] eqv.refl
attribute [symm] eqv.symm
attribute [trans] eqv.trans

attribute [congr] eqv.cons eqv.ap

open certificate

variables {G : Type*} [group G]

lemma inv_core_eq (a b : free_group) : inv_core a b = a⁻¹ ++ b :=
begin
  induction a with i a ih generalizing b,
  { simp [inv_def, inv_core] },
  { rw [inv_def] at *,
    rcases i with ⟨_,_|_⟩,
    { rw [inv_core, ih, inv_core, ih [_]],
      simp },
    { rw [inv_core, ih, inv_core, ih [_]],
      simp } }
end

lemma inv_core_cons_ff_eqv (i : ℕ) (a b : free_group) :
  eqv (inv_core (cons i ff a) b) (inv_core a (cons i tt b)) :=
by refl

lemma inv_core_cons_tt_eqv (i : ℕ) (a b : free_group) :
  eqv (inv_core (cons i tt a) b) (inv_core a (cons i ff b)) :=
by refl

lemma inv_core_one_eqv (b : free_group) :
  eqv (inv_core 1 b) b := by refl

lemma ap_one_eqv (a : free_group) : eqv (ap a 1) a := by simp [ap, one_def]

lemma one_ap_eqv (a : free_group) : eqv (ap 1 a) a := by simp [ap, one_def]

lemma one_inv_eqv : eqv (inv 1) 1 := eqv.refl _

lemma ap_cons_eqv {i : ℕ} {o : bool} {a b : free_group} :
  eqv (ap (cons i o a) b) (cons i o (ap a b)) :=
by simp [cons, ap]

lemma eval_eq_of_eqv (atoms : list G) {a b : free_group} (hab : eqv a b) :
  eval atoms a = eval atoms b :=
by induction hab; simp [eval, eval_append, *, ap, eval_cons, eval_inv, inv_core_eq] at *

local infixl `≡` :50 := free_group.eqv

lemma cert_eval_step_eqv (atoms : list G) (conj rel h)
  (c : certificate atoms) : (certificate.step conj rel h c).eval atoms ≡
  conj *' rel *' c.eval atoms *' inv_core conj 1 :=
eqv.refl _

lemma cert_eval_one_eqv (atoms : list G) : certificate.one.eval atoms ≡ 1 :=
eqv.refl _

meta def mk_free_group_simp_lemmas : tactic simp_lemmas :=
do sl : simp_lemmas ←
  ([``eqv.mul_inv_cancel, ``eqv.inv_mul_cancel,
    ``ap_one_eqv, ``one_ap_eqv, ``ap_cons_eqv,
    ``inv_core_cons_ff_eqv, ``inv_core_cons_tt_eqv,
    ``inv_core_one_eqv,
    ``cert_eval_step_eqv,
    ``cert_eval_one_eqv] : list name).mfoldl
  (λ (sl : simp_lemmas) n, sl.add_simp n)
  simp_lemmas.mk,
[``eqv.cons, ``eqv.inv_core, ``eqv.ap].mfoldl
  (λ (sl : simp_lemmas) n, sl.add_congr n)
  sl

run_cmd mk_free_group_simp_lemmas

open tactic expr

meta def free_group_simp (lhs : expr) (sl : simp_lemmas) : tactic expr :=
do
(lhs', prl) ← (simplify sl [] lhs (default _) ``eqv <|> return (lhs, `(eqv.refl %%lhs))),
trace lhs',
return prl
#print free_group_simp
def Gd : Type := sorry
instance : group Gd := sorry

run_cmd do sl ← mk_free_group_simp_lemmas,
  free_group_simp
    `(certificate.eval ([] : list Gd)
        (certificate.step [⟨1, ff⟩] 1 sorry certificate.one)) sl


end eqv

end free_group
end group_rel
