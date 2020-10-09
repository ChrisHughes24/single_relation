import data.list.chain data.int.basic tactic data.list.basic

variables {α : Type*}

open list

def reduced (l : list (α × ℤ)) : Prop :=
l.chain' (λ a b, a.1 ≠ b.1) ∧ ∀ a : α × ℤ, a ∈ l → a.2 ≠ 0

@[simp] lemma reduced_nil : reduced ([] : list (α × ℤ)) :=
⟨list.chain'_nil, λ _, false.elim⟩

lemma reduced_of_reduced_cons {a : α × ℤ} {l : list (α × ℤ)}
  (h : reduced (a :: l)) : reduced l :=
⟨(list.chain'_cons'.1 h.1).2, λ b hb, h.2 _ (mem_cons_of_mem _ hb)⟩

lemma reduced_cons_of_reduced_cons {a : α} {i j : ℤ} {l : list (α × ℤ)}
  (h : reduced ((a, i) :: l)) (hj : j ≠ 0) : reduced ((a, j) :: l) :=
⟨chain'_cons'.2 (chain'_cons'.1 h.1),
  begin
    rintros ⟨b, k⟩ hb,
    cases (mem_cons_iff _ _ _).1 hb with hb hb,
    { cc },
    { exact h.2 _ (mem_cons_of_mem _ hb) }
  end⟩

lemma reduced_cons_cons {a b : α} {i j : ℤ} {l : list (α × ℤ)} (hab : a ≠ b) (hi : i ≠ 0)
  (hbl : reduced ((b, j) :: l)) : reduced ((a, i) :: (b, j) :: l) :=
⟨chain'_cons.2 ⟨hab, hbl.1⟩,
  begin
    rintros ⟨c, k⟩ hc,
    cases (mem_cons_iff _ _ _).1 hc with hc hc,
    { cc },
    { exact hbl.2 _ hc }
  end⟩

lemma reduced_reverse {l : list (α × ℤ)} (h : reduced l) : reduced l.reverse :=
⟨chain'_reverse.2 $ by {convert h.1, simp [function.funext_iff, eq_comm] },
  by simpa using h.2⟩

@[simp] lemma reduced_reverse_iff {l : list (α × ℤ)} : reduced l.reverse ↔ reduced l :=
⟨λ h, by convert reduced_reverse h; simp, reduced_reverse⟩

variable (α)
def free_group : Type* := {l : list (α × ℤ) // reduced l}

namespace free_group

instance : has_one (free_group α) := ⟨⟨[], trivial, by simp⟩⟩

variables {α} [decidable_eq α]

def rcons : α × ℤ → list (α × ℤ) → list (α × ℤ)
| a []     := [a]
| a (b::l) :=
  if a.1 = b.1
    then let k := a.2 + b.2 in
      if k = 0
        then l
        else (a.1, k) :: l
    else a :: b :: l

-- def rconcat (a : α × ℤ) (l : list (α × ℤ)) : list (α × ℤ) :=
-- (rcons a l.reverse).reverse

def reduce : list (α × ℤ) → list (α × ℤ)
| []       := []
| (a :: l) := if a.2 = 0 then reduce l else rcons a (reduce l)

lemma reduced_rcons : ∀ {a : α × ℤ} {l : list (α × ℤ)},
  a.2 ≠ 0 → reduced l → reduced (rcons a l)
| (a, i) []            ha h := ⟨list.chain'_singleton _, by simp [rcons]; cc⟩
| (a, i) ((b, j) :: l) ha h := begin
  simp [rcons],
  split_ifs,
  { exact reduced_of_reduced_cons h },
  { subst h_1,
    exact reduced_cons_of_reduced_cons h h_2 },
  { exact reduced_cons_cons h_1 ha h }
end

-- lemma reduced_rconcat  {a : α × ℤ} {l : list (α × ℤ)}
--   (ha : a.2 ≠ 0) (hl : reduced l) : reduced (rconcat a l) :=
-- begin
--   rw [rconcat, reduced_reverse_iff],
--   exact reduced_rcons ha (reduced_reverse hl)
-- end

lemma reduced_reduce : ∀ l : list (α × ℤ), reduced (reduce l)
| []     := reduced_nil
| (a::l) := begin
  rw reduce,
  split_ifs,
  { exact reduced_reduce l },
  { exact reduced_rcons h (reduced_reduce l) }
end

lemma rcons_eq_cons : ∀ {a : α × ℤ} {l : list (α × ℤ)},
  reduced (a :: l) → rcons a l = a :: l
| a []     h := rfl
| a (b::l) h := if_neg (chain'_cons.1 h.1).1

-- lemma rconcat_eq_concat  {a : α × ℤ} {l : list (α × ℤ)}
--   (h : reduced (l ++ [a])) : rconcat a l = l ++ [a] :=
-- begin
--   rw [rconcat, rcons_eq_cons], simp,
--   convert reduced_reverse h, simp,
-- end

lemma rcons_reduce_eq_reduce_cons : ∀ {a : α × ℤ} {l : list (α × ℤ)},
  a.2 ≠ 0 → rcons a (reduce l) = reduce (a :: l)
| a []     ha := by simp [rcons, reduce, ha]
| a (b::l) ha := begin
  rw [reduce],
  split_ifs,
  { rw [reduce, if_neg ha, reduce, if_pos h] },
  { rw [reduce, if_neg ha, reduce, if_neg h] }
end

-- inductive rel : list (α × ℤ) → list (α × ℤ) → Prop
-- | refl : ∀ l, rel l l
-- | zero : ∀ {a : α}, rel [(a, 0)] []
-- | add : ∀ {a i j}, rel [(a, i), (a, j)] [(a, i + j)]
-- | append : ∀ {l₁ l₂ l₃ l₄}, rel l₁ l₂ → rel l₃ l₄ → rel (l₁ ++ l₃) (l₂ ++ l₄)
-- | symm : ∀ {l₁ l₂}, rel l₁ l₂ → rel l₂ l₁
-- | trans : ∀ {l₁ l₂ l₃}, rel l₁ l₂ → rel l₂ l₃ → rel l₁ l₃


-- attribute [refl] rel.refl
-- attribute [symm] rel.symm
-- attribute [trans] rel.trans



-- -- @[refl] lemma rel.refl : ∀ l : list (α × ℤ), rel l l := sorry

-- lemma rel_rcons_cons : ∀ (a : α × ℤ) (l : list (α × ℤ)),
--   rel (rcons a l) (a::l)
-- | a [] := rel.refl _
-- | (a, i) ((b,j)::l) := begin
--   rw rcons,
--   split_ifs,
--   { replace h : a = b := h, subst h,
--     show rel ([] ++ l) ([(a,i), (a, j)]  ++ l),
--     refine rel.append _ (rel.refl _),
--     symmetry,
--     exact rel.add.trans (h_1.symm ▸ rel.zero) },
--   { replace h : a = b := h, subst h,
--     show rel ([(a, i + j)] ++ l) ([(a, i), (a, j)] ++ l),
--     exact rel.append rel.add.symm (rel.refl _) },
--   { refl },
-- end

-- lemma rel_cons_of_rel {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) (a : α × ℤ) :
--   rel (a :: l₁) (a :: l₂) :=
-- show rel ([a] ++ l₁) ([a] ++ l₂), from rel.append (rel.refl _) h

-- lemma rel_rcons_cons_of_rel {a : α × ℤ} {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) :
--   rel (rcons a l₁) (a ::l₂) :=
-- (rel_rcons_cons a l₁).trans (rel_cons_of_rel h _)

-- lemma rel_reduce : ∀ l : list (α × ℤ), rel l (reduce l)
-- | [] := rel.refl _
-- | ((a, i)::l) := begin
--   rw reduce,
--   split_ifs,
--   { replace h : i = 0 := h, subst h,
--     show rel ([(a, 0)] ++ l) ([] ++ reduce l),
--     exact rel.append rel.zero (rel_reduce _) },
--   { exact (rel_rcons_cons_of_rel (rel_reduce _).symm).symm }
-- end

-- lemma reduce_eq_reduce_of_rel {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) : reduce l₁ = reduce l₂ :=
-- begin
--   induction h,
--   { refl },
--   { simp [reduce] },
--   { simp only [reduce],
--     split_ifs,
--     { refl },
--     { simp * at * },
--     { exfalso, omega },
--     { simp [rcons, *] },
--     { exfalso, omega },
--     { simp [rcons, *] },
--     { simp [rcons, *] },
--     { simp [rcons, *] } },
--   {  }


-- end

lemma reduce_eq_self_of_reduced : ∀ {l : list (α × ℤ)}, reduced l → reduce l = l
| []     h := rfl
| (a::l) h := by rw [← rcons_reduce_eq_reduce_cons (h.2 a (mem_cons_self _ _)),
    reduce_eq_self_of_reduced (reduced_of_reduced_cons h), rcons_eq_cons h]

lemma rcons_eq_reduce_cons {a : α × ℤ} {l : list (α × ℤ)}
  (ha : a.2 ≠ 0) (hl : reduced l) : rcons a l = reduce (a :: l) :=
by rw [← rcons_reduce_eq_reduce_cons ha, reduce_eq_self_of_reduced hl]

@[simp] lemma reduce_reduce (l : list (α × ℤ)) : reduce (reduce l) = reduce l :=
reduce_eq_self_of_reduced (reduced_reduce l)

@[simp] lemma reduce_cons_reduce_eq_reduce_cons (a : α × ℤ) (l : list (α × ℤ)) :
  reduce (a :: reduce l) = reduce (a :: l)  :=
if ha : a.2 = 0 then by rw [reduce, if_pos ha, reduce, if_pos ha, reduce_reduce]
else by rw [← rcons_reduce_eq_reduce_cons ha, ← rcons_reduce_eq_reduce_cons ha,
    reduce_reduce]

lemma length_rcons_le : ∀ (a : α × ℤ) (l : list (α × ℤ)),
  (rcons a l).length ≤ (a::l : list _).length
| a     []         := le_refl _
| (a,i) ((b,j)::l) := begin
  simp [rcons],
  split_ifs,
  { linarith },
  { simp },
  { simp }
end

lemma length_reduce_le : ∀ (l : list (α × ℤ)),
  (reduce l).length ≤ l.length
| []        := le_refl _
| [a]       := by { simp [reduce], split_ifs; simp [rcons] }
| (a::b::l) := begin
  simp only [reduce, rcons],
  split_ifs,
  { exact le_trans (length_reduce_le _)
      (le_trans (nat.le_succ _) (nat.le_succ _)) },
  { exact le_trans (length_rcons_le _ _) (nat.succ_le_succ
      (le_trans (length_reduce_le _) (nat.le_succ _))) },
  { exact le_trans (length_rcons_le _ _) (nat.succ_le_succ
      (le_trans (length_reduce_le _) (nat.le_succ _))) },
  { exact le_trans (length_rcons_le _ _) (nat.succ_le_succ
         (le_trans (length_rcons_le _ _) (nat.succ_le_succ
           (length_reduce_le _)))) }
end

lemma length_rcons_lt_or_eq_rcons : ∀ (a : α × ℤ) (l : list (α × ℤ)),
  (rcons a l).length < (a :: l : list _).length ∨ rcons a l = (a::l)
| a [] := or.inr rfl
| a (b::l) := begin
  simp only [rcons],
  split_ifs,
  { exact or.inl (nat.lt_succ_of_le (nat.le_succ _)) },
  { exact or.inl (nat.lt_succ_self _) },
  { simp }
end

lemma length_reduce_lt_or_eq_reduce : ∀ (l : list (α × ℤ)),
  (reduce l).length < l.length ∨ reduce l = l
| []        := or.inr rfl
| (a::l)    := begin
  simp only [reduce],
  split_ifs,
  { exact or.inl (nat.lt_succ_of_le (length_reduce_le _)) },
  { cases length_rcons_lt_or_eq_rcons a (reduce l) with h h,
    { exact or.inl (lt_of_lt_of_le h (nat.succ_le_succ (length_reduce_le _))) },
    { rw h,
      cases length_reduce_lt_or_eq_reduce l with h h,
      { exact or.inl (nat.succ_lt_succ h) },
      { rw h, right, refl } } }
end

lemma rcons_append : ∀ {a b : α × ℤ} {l₁ l₂ : list (α × ℤ)},
  rcons a ((b::l₁) ++ l₂) = rcons a (b::l₁) ++ l₂
| a b [] l₂ := begin
  simp [rcons], split_ifs; simp
end
| a b (c::l₁) l₂ := begin
  rw [cons_append, rcons],
  dsimp,
  split_ifs,
  { simp [rcons, *] },
  { simp [rcons, *] },
  { simp [rcons, *] }
end

lemma rcons_rcons_of_add_eq_zero {a : α} {i j : ℤ} : ∀ {l : list (α × ℤ)},
  i + j = 0 → reduced l → rcons (a, i) (rcons (a, j) l) = l
| []          hij hl := by simp [rcons, hij]
| ((b, k)::l) hij hl := begin
  simp only [rcons],
  split_ifs,
  { rw [← rcons_eq_cons hl, show a = b, from h, show i = k, by omega] },
  { simp only [rcons, if_pos rfl],
    rw [if_neg, ← add_assoc, hij, zero_add, show a = b, from h],
    have hk0 : k ≠ 0 := hl.2 (b, k) (mem_cons_self _ _),
    omega },
  { rw [rcons, if_pos rfl], dsimp, rw [if_pos hij] }
end

lemma rcons_rcons_of_add_ne_zero {a : α} {i j : ℤ} : ∀ {l : list (α × ℤ)},
  i + j ≠ 0 → i ≠ 0 → reduced l → rcons (a, i) (rcons (a, j) l) = rcons (a, i + j) l
| []          hij hi hl := by simp [rcons, hij]
| [(b, k)]    hij hi hl := begin
  simp only [rcons],
  split_ifs,
  { exfalso, omega },
  { simp [rcons], omega },
  { simp only [rcons, ← add_assoc, *, if_pos rfl] },
  { simp only [rcons, if_pos rfl, ← add_assoc, *],
    simp },
  { simp [rcons, if_neg hij, if_pos rfl] }
end
| ((b, k)::(c, m)::l) hij hi hl := begin
  have hbc : b ≠ c, from (chain'_cons.1 hl.1).1,
  simp only [rcons],
  split_ifs,
  { exfalso, omega },
  { simp [*, rcons] at *, omega },
  { simp [*, rcons, ← add_assoc] at * },
  { simp [*, rcons, ← add_assoc] },
  { simp [*, rcons] }
end

lemma reduce_rcons : ∀ {a : α × ℤ} (l : list (α × ℤ)), a.2 ≠ 0 →
  reduce (rcons a l) = rcons a (reduce l)
| a []     ha := by simp [rcons, reduce, ha]
| (a, i) [(b, j)]    hi := begin
    replace hi : i ≠ 0 := hi,
    simp only [reduce, rcons],
    split_ifs; simp [reduce, rcons, *] at *
  end
| (a,i) ((b,j)::l) hi := begin
  simp only [rcons],
  split_ifs,
  { rw [reduce, if_neg, h,
      rcons_rcons_of_add_eq_zero h_1 (reduced_reduce _)],
    omega },
  { simp only [reduce, if_neg h_1, reduce],
    split_ifs,
    { simp [h_2] },
    { rw [h, rcons_rcons_of_add_ne_zero h_1 hi (reduced_reduce _)] } },
  { rw [rcons_eq_reduce_cons hi (reduced_reduce _), reduce_cons_reduce_eq_reduce_cons] }
end

@[simp] lemma reduce_reduce_append_eq_reduce_append : ∀ (l₁ l₂ : list (α × ℤ)),
  reduce (reduce l₁ ++ l₂) = reduce (l₁ ++ l₂)
| []         l₂ := rfl
| (a::l₁) l₂ := begin
  simp only [reduce, cons_append],
  split_ifs with ha ha,
  { exact reduce_reduce_append_eq_reduce_append _ _ },
  { rw [← reduce_reduce_append_eq_reduce_append l₁ l₂],
    induction h : reduce l₁,
    { simp [rcons, rcons_eq_reduce_cons ha (reduced_reduce _)] },
    { rw [← rcons_append, reduce_rcons _ ha] } }
end

@[simp] lemma reduce_append_reduce_eq_reduce_append : ∀ {l₁ l₂ : list (α × ℤ)},
  reduce (l₁ ++ reduce l₂) = reduce (l₁ ++ l₂)
| []      l₂ := by simp
| (a::l₁) l₂ := by rw [cons_append, ← reduce_cons_reduce_eq_reduce_cons,
    reduce_append_reduce_eq_reduce_append,
    reduce_cons_reduce_eq_reduce_cons, cons_append]

/- TODO: Speed up, not the best definition, no need to reduce entire first list. -/
def mul_aux : list (α × ℤ) → list (α × ℤ) → list (α × ℤ)
| []        l₂ := l₂
| (a :: l₁) l₂ := rcons a (mul_aux l₁ l₂)

lemma reduced_mul_aux : ∀ {l₁ l₂ : list (α × ℤ)}, reduced l₁ →
  reduced l₂ → reduced (mul_aux l₁ l₂)
| []      l₂ _  h  := h
| (a::l₁) l₂ h₁ h₂ := reduced_rcons
  (h₁.2 _ (mem_cons_self _ _))
  (reduced_mul_aux (reduced_of_reduced_cons h₁) h₂)

lemma mul_aux_eq_reduce_append : ∀ {l₁ l₂ : list (α × ℤ)}, reduced l₁ →
  reduced l₂ → mul_aux l₁ l₂ = reduce (l₁ ++ l₂)
| []      l₂ _  h  := by simp [reduce, mul_aux, reduce_eq_self_of_reduced h]
| (a::l₁) l₂ h₁ h₂ :=
  by rw [mul_aux, mul_aux_eq_reduce_append (reduced_of_reduced_cons h₁) h₂,
    rcons_reduce_eq_reduce_cons (h₁.2 a (mem_cons_self _ _)), cons_append]

lemma mul_aux_assoc {l₁ l₂ l₃ : list (α × ℤ)}
  (h₁ : reduced l₁) (h₂ : reduced l₂) (h₃ : reduced l₃) :
  mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃) :=
begin
  rw [mul_aux_eq_reduce_append h₁ h₂, mul_aux_eq_reduce_append h₂ h₃,
    mul_aux_eq_reduce_append (reduced_reduce _) h₃,
    mul_aux_eq_reduce_append h₁ (reduced_reduce _)],
  simp [append_assoc]
end

instance : has_mul (free_group α) :=
⟨λ a b : free_group α, ⟨mul_aux a.1 b.1, reduced_mul_aux a.2 b.2⟩⟩

def inv_aux (l : list (α × ℤ)) : list (α × ℤ) :=
l.reverse.map (λ a, (a.1, -a.2))

lemma inv_aux_cons (a : α) (i : ℤ) (l : list (α × ℤ)) :
  inv_aux ((a, i) :: l) = inv_aux l ++ [(a, -i)] :=
by  simp [inv_aux]

lemma reduced_inv_aux {l : list (α × ℤ)} (hl : reduced l) : reduced (inv_aux l) :=
⟨(list.chain'_map _).2 (list.chain'_reverse.2 begin
  convert hl.1, simp [function.funext_iff, eq_comm],
end), begin
  rintros ⟨a, i⟩ ha,
  have := hl.2 (a, -i),
  finish [inv_aux]
end⟩

instance : has_inv (free_group α) :=
⟨λ a, ⟨inv_aux a.1, reduced_inv_aux a.2⟩⟩

lemma mul_aux_inv_aux_cancel : ∀ {l : list (α × ℤ)}, reduced l →
  mul_aux l (inv_aux l) = []
| []          hl := rfl
| ((a, i)::l) hal :=
have hi : i ≠ 0, from hal.2 (a, i) (mem_cons_self _ _),
have hl : reduced l, from reduced_of_reduced_cons hal,
begin
  rw [mul_aux_eq_reduce_append hal (reduced_inv_aux hal), inv_aux_cons, cons_append,
    ← append_assoc, ← reduce_cons_reduce_eq_reduce_cons,
    ← reduce_reduce_append_eq_reduce_append, reduce_cons_reduce_eq_reduce_cons,
    ← mul_aux_eq_reduce_append hl (reduced_inv_aux hl), mul_aux_inv_aux_cancel hl],
  simp [reduce, hi, rcons]
end

instance : group (free_group α) :=
{ mul := (*),
  inv := has_inv.inv,
  one := 1,
  mul_assoc := λ a b c, subtype.eq (mul_aux_assoc a.2 b.2 c.2),
  one_mul := λ ⟨_, _⟩, rfl,
  mul_one := λ ⟨_, _⟩, sorry,
  mul_left_inv := sorry }

lemma mul_def (a b : free_group α) : a * b = ⟨mul_aux a.1 b.1, reduced_mul_aux a.2 b.2⟩ := rfl

def of (a : α) : free_group α := ⟨[(a, 1)], by simp [reduced] { contextual := tt }⟩

@[elab_as_eliminator] lemma induction_on {P : free_group α → Prop}
  (g : free_group α)
  (h1 : P 1)
  (atom : ∀ a, P (of a))
  (atom_inv : ∀ a, P (of a)⁻¹)
  (hmul : ∀ a g, P g → P (of a * g)) :
  P g :=
begin
  cases g with l hl,
  induction l with a l ihl,
  { exact h1 },
  { cases a with a i,
    induction i using int.induction_on with i ihi i ihi,
    { simpa [reduced] using hl },
    { by_cases hi : i = 0,
      { subst i,
        convert hmul a ⟨l, reduced_of_reduced_cons hl⟩ (ihl (reduced_of_reduced_cons hl)),
        rw [mul_aux_eq_reduce_append (of a).2 (reduced_of_reduced_cons hl), of,
          cons_append, nil_append, ← reduce_eq_self_of_reduced hl, int.coe_nat_zero, zero_add] },
      { have hil : reduced ((a, i) :: l),
          from reduced_cons_of_reduced_cons hl (by norm_cast; exact hi),
        convert hmul a ⟨(a, i) :: l, hil⟩ (ihi hil),
        rw [mul_aux_eq_reduce_append (of a).2 hil, of, cons_append, nil_append,
          reduce, if_neg, reduce, if_neg, rcons_rcons_of_add_ne_zero],
         }, }
  }
end

variables {β : Type*} [decidable_eq β] (e : α → β)

def map : free_group α →* free_group β :=
{ to_fun := λ ⟨l, hl⟩, ⟨l.map e, _⟩ }

end free_group

