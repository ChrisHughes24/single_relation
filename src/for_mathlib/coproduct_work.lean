import data.list.chain data.int.basic tactic data.list.basic

variables {ι : Type*} {G : ι → Type*} [Π i, monoid (G i)]

open list

def reduced (l : list (Σ i, G i)) : Prop :=
l.chain' (λ a b, a.1 ≠ b.1) ∧ ∀ a : Σ i, G i, a ∈ l → a.2 ≠ 1

@[simp] lemma reduced_nil : reduced ([] : list (Σ i, G i)) :=
⟨list.chain'_nil, λ _, false.elim⟩

lemma reduced_of_reduced_cons {i : Σ i, G i} {l : list (Σ i, G i)}
  (h : reduced (i :: l)) : reduced l :=
⟨(list.chain'_cons'.1 h.1).2, λ b hb, h.2 _ (mem_cons_of_mem _ hb)⟩

lemma reduced_cons_of_reduced_cons {i : ι} {a b : G i} {l : list (Σ i, G i)}
  (h : reduced (⟨i, a⟩ :: l)) (hb : b ≠ 1) : reduced (⟨i, b⟩ :: l) :=
⟨chain'_cons'.2 (chain'_cons'.1 h.1),
  begin
    rintros ⟨k, c⟩ hk,
    cases (mem_cons_iff _ _ _).1 hk with hk hk,
    { simp only at hk,
      rcases hk with ⟨rfl, h⟩,
      simp * at * },
    { exact h.2 _ (mem_cons_of_mem _ hk) }
  end⟩

lemma reduced_cons_cons {i j : ι} {a : G i} {b : G j}
  {l : list (Σ i, G i)} (hij : i ≠ j) (ha : a ≠ 1)
  (hbl : reduced (⟨j, b⟩ :: l)) : reduced (⟨i, a⟩ :: ⟨j, b⟩ :: l) :=
⟨chain'_cons.2 ⟨hij, hbl.1⟩,
  begin
    rintros ⟨k, c⟩ hk,
    cases (mem_cons_iff _ _ _).1 hk with hk hk,
    { simp only at hk,
      rcases hk with ⟨rfl, h⟩,
      simp * at * },
    { exact hbl.2 _ hk }
  end⟩

lemma reduced_reverse {l : list (Σ i, G i)} (h : reduced l) : reduced l.reverse :=
⟨chain'_reverse.2 $ by {convert h.1, simp [function.funext_iff, eq_comm] },
  by simpa using h.2⟩

@[simp] lemma reduced_reverse_iff {l : list (Σ i, G i)} : reduced l.reverse ↔ reduced l :=
⟨λ h, by convert reduced_reverse h; simp, reduced_reverse⟩

variable (G)
def coprod : Type* := {l : list (Σ i, G i) // reduced l}

namespace coprod

instance : has_one (coprod G) := ⟨⟨[], trivial, by simp⟩⟩

variables {ι} [decidable_eq ι] {G} [Π i, decidable_eq (G i)]

def rcons : (Σ i, G i) → list (Σ i, G i) → list (Σ i, G i)
| i []     := [i]
| i (j::l) :=
  if hij : i.1 = j.1
    then let c := i.2 * cast (congr_arg G hij).symm j.2 in
      if c = 1
        then l
        else ⟨i.1, c⟩ :: l
    else i::j::l

-- def rconcat (a : Σ i, G i) (l : list (Σ i, G i)) : list (Σ i, G i) :=
-- (rcons a l.reverse).reverse

def reduce : list (Σ i, G i) → list (Σ i, G i)
| []       := []
| (i :: l) := if h : i.2 = 1 then reduce l else rcons i (reduce l)

lemma reduced_rcons : ∀ {i : Σ i, G i} {l : list (Σ i, G i)},
  i.2 ≠ 1 → reduced l → reduced (rcons i l)
| ⟨i, a⟩ []            hi h := ⟨list.chain'_singleton _,
  begin
    rintros ⟨j, b⟩ hj,
    simp only [rcons, list.mem_singleton] at hj,
    rcases hj with ⟨rfl, h⟩,
    simp * at *
  end⟩
| ⟨i, a⟩ (⟨j, b⟩ :: l) hi h := begin
  simp [rcons],
  split_ifs,
  { exact reduced_of_reduced_cons h },
  { dsimp only at h_1,
    subst h_1,
    exact reduced_cons_of_reduced_cons h h_2 },
  { exact reduced_cons_cons h_1 hi h }
end

-- lemma reduced_rconcat  {a : Σ i, G i} {l : list (Σ i, G i)}
--   (ha : a.2 ≠ 0) (hl : reduced l) : reduced (rconcat a l) :=
-- begin
--   rw [rconcat, reduced_reverse_iff],
--   exact reduced_rcons ha (reduced_reverse hl)
-- end

lemma reduced_reduce : ∀ l : list (Σ i, G i), reduced (reduce l)
| []     := reduced_nil
| (a::l) := begin
  rw reduce,
  split_ifs,
  { exact reduced_reduce l },
  { exact reduced_rcons h (reduced_reduce l) }
end

lemma rcons_eq_cons : ∀ {i : Σ i, G i} {l : list (Σ i, G i)},
  reduced (i :: l) → rcons i l = i :: l
| i []     h := rfl
| i (j::l) h := dif_neg (chain'_cons.1 h.1).1

-- lemma rconcat_eq_concat  {a : Σ i, G i} {l : list (Σ i, G i)}
--   (h : reduced (l ++ [a])) : rconcat a l = l ++ [a] :=
-- begin
--   rw [rconcat, rcons_eq_cons], simp,
--   convert reduced_reverse h, simp,
-- end

lemma rcons_reduce_eq_reduce_cons : ∀ {i : Σ i, G i} {l : list (Σ i, G i)},
  i.2 ≠ 1 → rcons i (reduce l) = reduce (i :: l)
| a []     ha := by simp [rcons, reduce, ha]
| a (b::l) ha := begin
  rw [reduce],
  split_ifs,
  { rw [reduce, if_neg ha, reduce, if_pos h] },
  { rw [reduce, if_neg ha, reduce, if_neg h] }
end

-- inductive rel : list (Σ i, G i) → list (Σ i, G i) → Prop
-- | refl : ∀ l, rel l l
-- | zero : ∀ {a : ι}, rel [(a, 0)] []
-- | add : ∀ {a i j}, rel [(a, i), (a, j)] [(a, i + j)]
-- | append : ∀ {l₁ l₂ l₃ l₄}, rel l₁ l₂ → rel l₃ l₄ → rel (l₁ ++ l₃) (l₂ ++ l₄)
-- | symm : ∀ {l₁ l₂}, rel l₁ l₂ → rel l₂ l₁
-- | trans : ∀ {l₁ l₂ l₃}, rel l₁ l₂ → rel l₂ l₃ → rel l₁ l₃


-- attribute [refl] rel.refl
-- attribute [symm] rel.symm
-- attribute [trans] rel.trans



-- -- @[refl] lemma rel.refl : ∀ l : list (Σ i, G i), rel l l := sorry

-- lemma rel_rcons_cons : ∀ (a : Σ i, G i) (l : list (Σ i, G i)),
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

-- lemma rel_cons_of_rel {l₁ l₂ : list (Σ i, G i)} (h : rel l₁ l₂) (a : Σ i, G i) :
--   rel (a :: l₁) (a :: l₂) :=
-- show rel ([a] ++ l₁) ([a] ++ l₂), from rel.append (rel.refl _) h

-- lemma rel_rcons_cons_of_rel {a : Σ i, G i} {l₁ l₂ : list (Σ i, G i)} (h : rel l₁ l₂) :
--   rel (rcons a l₁) (a ::l₂) :=
-- (rel_rcons_cons a l₁).trans (rel_cons_of_rel h _)

-- lemma rel_reduce : ∀ l : list (Σ i, G i), rel l (reduce l)
-- | [] := rel.refl _
-- | ((a, i)::l) := begin
--   rw reduce,
--   split_ifs,
--   { replace h : i = 0 := h, subst h,
--     show rel ([(a, 0)] ++ l) ([] ++ reduce l),
--     exact rel.append rel.zero (rel_reduce _) },
--   { exact (rel_rcons_cons_of_rel (rel_reduce _).symm).symm }
-- end

-- lemma reduce_eq_reduce_of_rel {l₁ l₂ : list (Σ i, G i)} (h : rel l₁ l₂) : reduce l₁ = reduce l₂ :=
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

lemma reduce_eq_self_of_reduced : ∀ {l : list (Σ i, G i)}, reduced l → reduce l = l
| []     h := rfl
| (a::l) h := by rw [← rcons_reduce_eq_reduce_cons (h.2 a (mem_cons_self _ _)),
    reduce_eq_self_of_reduced (reduced_of_reduced_cons h), rcons_eq_cons h]

lemma rcons_eq_reduce_cons {i : Σ i, G i} {l : list (Σ i, G i)}
  (ha : i.2 ≠ 1) (hl : reduced l) : rcons i l = reduce (i :: l) :=
by rw [← rcons_reduce_eq_reduce_cons ha, reduce_eq_self_of_reduced hl]

@[simp] lemma reduce_reduce (l : list (Σ i, G i)) : reduce (reduce l) = reduce l :=
reduce_eq_self_of_reduced (reduced_reduce l)

@[simp] lemma reduce_cons_reduce_eq_reduce_cons (i : Σ i, G i) (l : list (Σ i, G i)) :
  reduce (i :: reduce l) = reduce (i :: l)  :=
if ha : i.2 = 1 then by rw [reduce, if_pos ha, reduce, if_pos ha, reduce_reduce]
else by rw [← rcons_reduce_eq_reduce_cons ha, ← rcons_reduce_eq_reduce_cons ha,
    reduce_reduce]

lemma length_rcons_le : ∀ (i : Σ i, G i) (l : list (Σ i, G i)),
  (rcons i l).length ≤ (i::l : list _).length
| i      []          := le_refl _
| ⟨i, a⟩ (⟨j, b⟩::l) := begin
  simp [rcons],
  split_ifs,
  { linarith },
  { simp },
  { simp }
end

lemma length_reduce_le : ∀ (l : list (Σ i, G i)),
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

lemma length_rcons_lt_or_eq_rcons : ∀ (i : Σ i, G i) (l : list (Σ i, G i)),
  (rcons i l).length < (i :: l : list _).length ∨ rcons i l = (i::l)
| i [] := or.inr rfl
| i (j::l) := begin
  simp only [rcons],
  split_ifs,
  { exact or.inl (nat.lt_succ_of_le (nat.le_succ _)) },
  { exact or.inl (nat.lt_succ_self _) },
  { simp }
end

lemma length_reduce_lt_or_eq_reduce : ∀ (l : list (Σ i, G i)),
  (reduce l).length < l.length ∨ reduce l = l
| []        := or.inr rfl
| (i::l)    := begin
  simp only [reduce],
  split_ifs,
  { exact or.inl (nat.lt_succ_of_le (length_reduce_le _)) },
  { cases length_rcons_lt_or_eq_rcons i (reduce l) with h h,
    { exact or.inl (lt_of_lt_of_le h (nat.succ_le_succ (length_reduce_le _))) },
    { rw h,
      cases length_reduce_lt_or_eq_reduce l with h h,
      { exact or.inl (nat.succ_lt_succ h) },
      { rw h, right, refl } } }
end

lemma rcons_append : ∀ {i j : Σ i, G i} {l₁ l₂ : list (Σ i, G i)},
  rcons i ((j::l₁) ++ l₂) = rcons i (j::l₁) ++ l₂
| i j [] l₂ := begin
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

lemma rcons_rcons_of_add_eq_zero {i : ι} {a b : G i} : ∀ {l : list (Σ i, G i)},
  a * b = 1 → reduced l → rcons ⟨i, a⟩ (rcons ⟨i, b⟩ l) = l
| []          hab hl := by simp [rcons, cast, hab]
| (⟨j, c⟩::l) hab hl := begin
  simp only [rcons],
  split_ifs,
  { dsimp only at h,
    subst h,
    rw [← rcons_eq_cons hl, left_inv_eq_right_inv hab h_1, cast_eq] },
  { dsimp only at h,
    subst h,
    simp only [rcons, dif_pos rfl],
    rw [cast_eq, cast_eq, if_neg, ← mul_assoc, hab, one_mul],
    { rw [← mul_assoc, hab, one_mul],
      exact hl.2 ⟨i, c⟩ (mem_cons_self _ _) } },
  { rw [rcons, dif_pos rfl, cast_eq], dsimp, rw [if_pos hab] }
end

lemma rcons_rcons_of_add_ne_zero {i : ι} {a b : G i} : ∀ {l : list (Σ i, G i)},
  a * b ≠ 1 → a ≠ 1 → reduced l → rcons ⟨i, a⟩ (rcons ⟨i, b⟩ l) = rcons ⟨i, a * b⟩ l
| []          hab ha hl := by simp [rcons, hab, cast_eq]
| [⟨j, c⟩]    hab ha hl := begin
  simp only [rcons],
  split_ifs,
  { rw [mul_assoc, h_1, mul_one] at h_2,
    exact (ha h_2).elim },
  { simp [rcons, mul_assoc, h_1] },
  { simp only [rcons, ← mul_assoc, *, dif_pos rfl, cast_eq, if_pos rfl] },
  { dsimp only at h,
    subst h,
    simp only [rcons, dif_pos rfl, ← mul_assoc, *, cast_eq] at *,
    simp },
  { simp [rcons, if_neg hab, if_pos rfl, cast_eq] }
end
| (⟨j, c⟩::⟨k, d⟩::l) hab ha hl := begin
  have hjk : j ≠ k, from (chain'_cons.1 hl.1).1,
  dsimp only [rcons],
  split_ifs,
  { rw [mul_assoc, h_1, mul_one] at h_2,
    exact (ha h_2).elim },
  { dsimp [rcons],
    subst h,
    simp [*, rcons, mul_assoc] at * },
  { simp [*, rcons, ← mul_assoc, cast_eq] at * },
  { simp [*, rcons, ← mul_assoc, cast_eq] },
  { simp [*, rcons, cast_eq] }
end

lemma reduce_rcons : ∀ {i : Σ i, G i} (l : list (Σ i, G i)), i.2 ≠ 1 →
  reduce (rcons i l) = rcons i (reduce l)
| i []               hi := by simp [rcons, reduce, hi]
| ⟨i, a⟩ [⟨j, b⟩]    ha := begin
    replace ha : a ≠ 1 := ha,
    dsimp only [reduce, rcons],
    by_cases hij : i = j,
    { subst hij,
      split_ifs;
      simp [*, reduce, rcons, cast_eq] at * },
    { simp [hij, reduce, rcons, ha] }
  end
| ⟨i, a⟩ (⟨j, b⟩::l) ha := begin
  dsimp only [rcons],
  split_ifs,
  { subst h,
    rw [cast_eq] at h_1,
    rw [reduce, if_neg, rcons_rcons_of_add_eq_zero h_1 (reduced_reduce _)],
    { refine λ hb : b = 1, _,
      rw [hb, mul_one] at h_1,
      exact ha h_1 } },
  { subst h,
    rw [reduce, if_neg h_1, reduce],
    split_ifs,
    { erw [cast_eq, show b = 1, from h, mul_one] },
    { rw cast_eq at h_1,
      rw [rcons_rcons_of_add_ne_zero h_1 ha (reduced_reduce l), cast_eq], } },
  { rw [rcons_eq_reduce_cons ha (reduced_reduce _), reduce_cons_reduce_eq_reduce_cons] }
end

@[simp] lemma reduce_reduce_append_eq_reduce_append : ∀ (l₁ l₂ : list (Σ i, G i)),
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

@[simp] lemma reduce_append_reduce_eq_reduce_append : ∀ {l₁ l₂ : list (Σ i, G i)},
  reduce (l₁ ++ reduce l₂) = reduce (l₁ ++ l₂)
| []      l₂ := by simp
| (a::l₁) l₂ := by rw [cons_append, ← reduce_cons_reduce_eq_reduce_cons,
    reduce_append_reduce_eq_reduce_append,
    reduce_cons_reduce_eq_reduce_cons, cons_append]

/- TODO: Speed up, not the best definition, no need to reduce entire first list. -/
def mul_aux : list (Σ i, G i) → list (Σ i, G i) → list (Σ i, G i)
| []        l₂ := l₂
| (i :: l₁) l₂ := rcons i (mul_aux l₁ l₂)

lemma reduced_mul_aux : ∀ {l₁ l₂ : list (Σ i, G i)}, reduced l₁ →
  reduced l₂ → reduced (mul_aux l₁ l₂)
| []      l₂ _  h  := h
| (i::l₁) l₂ h₁ h₂ := reduced_rcons
  (h₁.2 _ (mem_cons_self _ _))
  (reduced_mul_aux (reduced_of_reduced_cons h₁) h₂)

lemma mul_aux_eq_reduce_append : ∀ {l₁ l₂ : list (Σ i, G i)}, reduced l₁ →
  reduced l₂ → mul_aux l₁ l₂ = reduce (l₁ ++ l₂)
| []      l₂ _  h  := by simp [reduce, mul_aux, reduce_eq_self_of_reduced h]
| (i::l₁) l₂ h₁ h₂ :=
  by rw [mul_aux, mul_aux_eq_reduce_append (reduced_of_reduced_cons h₁) h₂,
    rcons_reduce_eq_reduce_cons (h₁.2 i (mem_cons_self _ _)), cons_append]

lemma mul_aux_assoc {l₁ l₂ l₃ : list (Σ i, G i)}
  (h₁ : reduced l₁) (h₂ : reduced l₂) (h₃ : reduced l₃) :
  mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃) :=
begin
  rw [mul_aux_eq_reduce_append h₁ h₂, mul_aux_eq_reduce_append h₂ h₃,
    mul_aux_eq_reduce_append (reduced_reduce _) h₃,
    mul_aux_eq_reduce_append h₁ (reduced_reduce _)],
  simp [append_assoc]
end

lemma mul_aux_nil : ∀ {l₁ : list (Σ i, G i)} (h : reduced l₁), mul_aux l₁ [] = l₁
| []     _ := rfl
| (i::l) h :=
  by rw [mul_aux, mul_aux_nil (reduced_of_reduced_cons h), rcons_eq_cons h]

instance : has_mul (coprod G) :=
⟨λ a b : coprod G, ⟨mul_aux a.1 b.1, reduced_mul_aux a.2 b.2⟩⟩

instance : monoid (coprod G) :=
{ mul := (*),
  one := 1,
  mul_assoc := λ a b c, subtype.eq (mul_aux_assoc a.2 b.2 c.2),
  one_mul := λ ⟨_, _⟩, rfl,
  mul_one := λ a, subtype.eq (mul_aux_nil a.2) }

-- def inv_aux (l : list (Σ i, G i)) : list (Σ i, G i) :=
-- l.reverse.map (λ a, (a.1, -a.2))

-- lemma inv_aux_cons (a : ι) (i : ℤ) (l : list (Σ i, G i)) :
--   inv_aux ((a, i) :: l) = inv_aux l ++ [(a, -i)] :=
-- by  simp [inv_aux]

-- lemma reduced_inv_aux {l : list (Σ i, G i)} (hl : reduced l) : reduced (inv_aux l) :=
-- ⟨(list.chain'_map _).2 (list.chain'_reverse.2 begin
--   convert hl.1, simp [function.funext_iff, eq_comm],
-- end), begin
--   rintros ⟨a, i⟩ ha,
--   have := hl.2 (a, -i),
--   finish [inv_aux]
-- end⟩

-- instance : has_inv (coprod ι) :=
-- ⟨λ a, ⟨inv_aux a.1, reduced_inv_aux a.2⟩⟩

-- lemma mul_aux_inv_aux_cancel : ∀ {l : list (Σ i, G i)}, reduced l →
--   mul_aux l (inv_aux l) = []
-- | []          hl := rfl
-- | ((a, i)::l) hal :=
-- have hi : i ≠ 0, from hal.2 (a, i) (mem_cons_self _ _),
-- have hl : reduced l, from reduced_of_reduced_cons hal,
-- begin
--   rw [mul_aux_eq_reduce_append hal (reduced_inv_aux hal), inv_aux_cons, cons_append,
--     ← append_assoc, ← reduce_cons_reduce_eq_reduce_cons,
--     ← reduce_reduce_append_eq_reduce_append, reduce_cons_reduce_eq_reduce_cons,
--     ← mul_aux_eq_reduce_append hl (reduced_inv_aux hl), mul_aux_inv_aux_cancel hl],
--   simp [reduce, hi, rcons]
-- end

-- instance : group (coprod ι) :=
-- { mul := (*),
--   inv := has_inv.inv,
--   one := 1,
--   mul_assoc := λ a b c, subtype.eq (mul_aux_assoc a.2 b.2 c.2),
--   one_mul := λ ⟨_, _⟩, rfl,
--   mul_one := λ ⟨_, _⟩, sorry,
--   mul_left_inv := sorry }

-- lemma mul_def (a b : coprod ι) : a * b = ⟨mul_aux a.1 b.1, reduced_mul_aux a.2 b.2⟩ := rfl

-- def of (a : ι) : coprod ι := ⟨[(a, 1)], by simp [reduced] { contextual := tt }⟩

-- @[elab_as_eliminator] lemma induction_on {P : coprod ι → Prop}
--   (g : coprod ι)
--   (h1 : P 1)
--   (atom : ∀ a, P (of a))
--   (atom_inv : ∀ a, P (of a)⁻¹)
--   (hmul : ∀ a g, P g → P (of a * g)) :
--   P g :=
-- begin
--   cases g with l hl,
--   induction l with a l ihl,
--   { exact h1 },
--   { cases a with a i,
--     induction i using int.induction_on with i ihi i ihi,
--     { simpa [reduced] using hl },
--     { by_cases hi : i = 0,
--       { subst i,
--         convert hmul a ⟨l, reduced_of_reduced_cons hl⟩ (ihl (reduced_of_reduced_cons hl)),
--         rw [mul_aux_eq_reduce_append (of a).2 (reduced_of_reduced_cons hl), of,
--           cons_append, nil_append, ← reduce_eq_self_of_reduced hl, int.coe_nat_zero, zero_add] },
--       { have hil : reduced ((a, i) :: l),
--           from reduced_cons_of_reduced_cons hl (by norm_cast; exact hi),
--         convert hmul a ⟨(a, i) :: l, hil⟩ (ihi hil),
--         rw [mul_aux_eq_reduce_append (of a).2 hil, of, cons_append, nil_append,
--           reduce, if_neg, reduce, if_neg, rcons_rcons_of_add_ne_zero],
--          }, }
--   }
-- end

-- variables {β : Type*} [decidable_eq β] (e : ι → β)

-- def map : coprod ι →* coprod β :=
-- { to_fun := λ ⟨l, hl⟩, ⟨l.map e, _⟩ }

-- end coprod

