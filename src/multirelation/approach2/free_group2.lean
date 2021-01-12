import algebra.group
import data.list.rotate

@[reducible] def free_group := list (ℕ × bool)

namespace group_rel
namespace free_group
open native

meta def to_expr (w : free_group) : expr :=
reflect (show list (ℕ × bool), from w)

instance : has_one (free_group) := ⟨[]⟩

lemma one_def : (1 : free_group) = [] := rfl

-- inv_core a b is a⁻¹ * b
def inv_core : free_group → free_group → free_group
| []            l  := l
| (⟨i, n⟩::l₁)  l₂ := inv_core l₁ (⟨i, bnot n⟩::l₂)

instance : has_inv free_group :=
⟨λ l, inv_core l []⟩

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
  (h : eval l [⟨x, ff⟩] = eval l r):
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
  sorry
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

end free_group
end group_rel
