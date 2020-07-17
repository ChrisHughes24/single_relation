import data.list.chain data.int.basic tactic

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

def rconcat (a : α × ℤ) (l : list (α × ℤ)) : list (α × ℤ) :=
(rcons a l.reverse).reverse

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

lemma reduced_rconcat  {a : α × ℤ} {l : list (α × ℤ)}
  (ha : a.2 ≠ 0) (hl : reduced l) : reduced (rconcat a l) :=
begin
  rw [rconcat, reduced_reverse_iff],
  exact reduced_rcons ha (reduced_reverse hl)
end

lemma reduced_reduce : ∀ l : list (α × ℤ), reduced (reduce l)
| []     := reduced_nil
| [a]    := begin simp [reduced, reduce], end
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

lemma rconcat_eq_concat  {a : α × ℤ} {l : list (α × ℤ)}
  (h : reduced (l ++ [a])) : rconcat a l = l ++ [a] :=
begin
  rw [rconcat, rcons_eq_cons], simp,
  convert reduced_reverse h, simp,
end

lemma rcons_reduce_eq_reduce_cons : ∀ {a : α × ℤ} {l : list (α × ℤ)},
  a.2 ≠ 0 → rcons a (reduce l) = reduce (a :: l)
| a []     ha := by simp [rcons, reduce, ha]
| a (b::l) ha := begin
  rw [reduce],
  split_ifs,
  { rw [reduce, if_neg ha, reduce, if_pos h] },
  { rw [reduce, if_neg ha, reduce, if_neg h] }
end

inductive rel : list (α × ℤ) → list (α × ℤ) → Prop
| refl : ∀ l, rel l l
| zero : ∀ {a : α}, rel [(a, 0)] []
| add : ∀ {a i j}, rel [(a, i), (a, j)] [(a, i + j)]
| append : ∀ {l₁ l₂ l₃ l₄}, rel l₁ l₂ → rel l₃ l₄ → rel (l₁ ++ l₃) (l₂ ++ l₄)
| symm : ∀ {l₁ l₂}, rel l₁ l₂ → rel l₂ l₁
| trans : ∀ {l₁ l₂ l₃}, rel l₁ l₂ → rel l₂ l₃ → rel l₁ l₃


attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans



-- @[refl] lemma rel.refl : ∀ l : list (α × ℤ), rel l l := sorry

lemma rel_rcons_cons : ∀ (a : α × ℤ) (l : list (α × ℤ)),
  rel (rcons a l) (a::l)
| a [] := rel.refl _
| (a, i) ((b,j)::l) := begin
  rw rcons,
  split_ifs,
  { replace h : a = b := h, subst h,
    show rel ([] ++ l) ([(a,i), (a, j)]  ++ l),
    refine rel.append _ (rel.refl _),
    symmetry,
    exact rel.add.trans (h_1.symm ▸ rel.zero) },
  { replace h : a = b := h, subst h,
    show rel ([(a, i + j)] ++ l) ([(a, i), (a, j)] ++ l),
    exact rel.append rel.add.symm (rel.refl _) },
  { refl },
end

lemma rel_cons_of_rel {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) (a : α × ℤ) :
  rel (a :: l₁) (a :: l₂) :=
show rel ([a] ++ l₁) ([a] ++ l₂), from rel.append (rel.refl _) h

lemma rel_rcons_cons_of_rel {a : α × ℤ} {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) :
  rel (rcons a l₁) (a ::l₂) :=
(rel_rcons_cons a l₁).trans (rel_cons_of_rel h _)

lemma rel_reduce : ∀ l : list (α × ℤ), rel l (reduce l)
| [] := rel.refl _
| ((a, i)::l) := begin
  rw reduce,
  split_ifs,
  { replace h : i = 0 := h, subst h,
    show rel ([(a, 0)] ++ l) ([] ++ reduce l),
    exact rel.append rel.zero (rel_reduce _) },
  { exact (rel_rcons_cons_of_rel (rel_reduce _).symm).symm }
end

lemma reduce_eq_reduce_of_rel {l₁ l₂ : list (α × ℤ)} (h : rel l₁ l₂) : reduce l₁ = reduce l₂ :=
begin
  induction h,
  { refl },
  { simp [reduce] },
  { simp only [reduce],
    split_ifs,
    { refl },
    { simp * at * },
    { exfalso, omega },
    { simp [rcons, *] },
    { exfalso, omega },
    { simp [rcons, *] },
    { simp [rcons, *] },
    { simp [rcons, *] } },
  {  }


end


lemma reduce_eq_self_of_reduced : ∀ {l : list (α × ℤ)}, reduced l → reduce l = l
| []     h := rfl
| (a::l) h := by rw [← rcons_reduce_eq_reduce_cons (h.2 a (mem_cons_self _ _)),
    reduce_eq_self_of_reduced (reduced_of_reduced_cons h), rcons_eq_cons h]

lemma rcons_eq_reduce_cons {a : α × ℤ} {l : list (α × ℤ)}
  (ha : a.2 ≠ 0) (hl : reduced l) : rcons a l = reduce (a :: l) :=
by rw [← rcons_reduce_eq_reduce_cons ha, reduce_eq_self_of_reduced hl]

@[simp] lemma reduce_reduce (l : list (α × ℤ)) : reduce (reduce l) = reduce l :=
reduce_eq_self_of_reduced (reduced_reduce l)

lemma reduce_cons_reduce_eq_reduce_cons (a : α × ℤ) (l : list (α × ℤ)) :
  reduce (a :: reduce l) = reduce (a :: l)  :=
if ha : a.2 = 0 then by rw [reduce, if_pos ha, reduce, if_pos ha, reduce_reduce]
else by rw [← rcons_reduce_eq_reduce_cons ha, ← rcons_reduce_eq_reduce_cons ha,
    reduce_reduce]


lemma reduce_reduce_concat_eq_reduce_concat  : ∀ (l : list (α × ℤ)), ∀ (a : α × ℤ),
  reduce (reduce l ++ [a]) = reduce (l ++ [a])
| [] a := rfl
| [a] b := begin simp [reduce], split_ifs; simp [reduce, *, rcons] end
| (a::b::l) c := begin
  simp only [reduce, cons_append],
  split_ifs,
  { exact reduce_reduce_concat_eq_reduce_concat _ _ },
  { rw [rcons_eq_reduce_cons h_1 (reduced_reduce _),
      reduce_reduce_concat_eq_reduce_concat,
      rcons_eq_reduce_cons h_1 (reduced_reduce _),
      cons_append, ← reduce_cons_reduce_eq_reduce_cons,
      reduce_reduce_concat_eq_reduce_concat] },
  { rw [rcons_eq_reduce_cons h (reduced_reduce _),
      reduce_reduce_concat_eq_reduce_concat,
      rcons_eq_reduce_cons h (reduced_reduce _),
      cons_append, ← reduce_cons_reduce_eq_reduce_cons,
      reduce_reduce_concat_eq_reduce_concat] },
  { rw [rcons_eq_reduce_cons h (reduced_rcons h_1 (reduced_reduce _)),
      rcons_eq_reduce_cons h_1 (reduced_reduce _),
      rcons_eq_reduce_cons h (reduced_rcons h_1 (reduced_reduce _)),
      rcons_eq_reduce_cons h_1 (reduced_reduce _),
      reduce_cons_reduce_eq_reduce_cons,
      reduce_cons_reduce_eq_reduce_cons,
      ← reduce_reduce_concat_eq_reduce_concat l c,
      ← reduce_cons_reduce_eq_reduce_cons], }

end
-- list.reverse_rec_on l (by simp [reduce])
-- begin
--   assume l b ih a,

-- end
-- begin
--   intro a,
--   induction l with b l ih generalizing a,
--   { simp [reduce] },
--   { simp [reduce],
--     split_ifs,
--     { exact ih a },
--     {  } }

-- end

lemma reduce_reduce_append_eq_reduce_append : ∀ {l₁ l₂ : list (α × ℤ)},
  reduce (l₁ ++ reduce l₂) = reduce (l₁ ++ l₂)
| []      l₂ := by simp
| (a::l₁) l₂ := by rw [cons_append, ← reduce_cons_reduce_eq_reduce_cons,
    reduce_reduce_append_eq_reduce_append,
    reduce_cons_reduce_eq_reduce_cons, cons_append]

lemma reduce_reduce_append_eq_reduce_append' : ∀ (l₁ l₂ : list (α × ℤ)),
  reduce (reduce l₁ ++ l₂) = reduce (l₁ ++ l₂)
| l₁ []         := by simp
| l₁ [a]        := begin  end
| l₁ (a::b::l₂) := show reduce (reduce l₁ ++ ([a] ++ (b::l₂))) = reduce (l₁ ++ a :: b::l₂),
begin
  rw [← append_assoc, ← reduce_reduce_append_eq_reduce_append' _ (b :: l₂),
    reduce_reduce_append_eq_reduce_append' l₁ [a],
    reduce_reduce_append_eq_reduce_append'],
  simp
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, list.length x.2)⟩] }

lemma reduce_reverse : ∀ {l : list (α × ℤ)}, reduce (reverse l) = reverse (reduce l)
| [] := rfl
| [a] := begin
  simp [reduce],
  split_ifs; simp [reduce_cons],
end
| (a::b::l) := begin
  rw [reduce],
  split_ifs,


end

lemma reduce_reduce_cons : ∀ (a : α × ℤ) (l : list (α × ℤ)),
  reduce (reduce_cons a l) = reduce (a :: l)
| a [] := rfl
| a (b::l) := begin
  simp [reduce, reduce_cons],
  split_ifs,
  { refl },
  { exfalso, omega },
  { exfalso, omega },
  { rw [reduce_cons_reduce_eq_reduce_cons h_3,
      reduce_cons_reduce_eq_reduce_cons h_2],
       }

end


def mul_aux : list (α × ℤ) → list (α × ℤ) → list (α × ℤ)
| []        l₂ := l₂
| (a :: l₁) l₂ := reduce_cons a (mul_aux l₁ l₂)

lemma mul_aux_reduced : ∀ {l₁ l₂ : list (α × ℤ)}, reduced l₁ →
  reduced l₂ → reduced (mul_aux l₁ l₂)
| []      l₂ _  h  := h
| (a::l₁) l₂ h₁ h₂ := reduced_reduce_cons
  (h₁.2 _ (mem_cons_self _ _))
  (mul_aux_reduced (reduced_of_reduced_cons h₁) h₂)

lemma mul_aux_eq_reduce_append : ∀ {l₁ l₂ : list (α × ℤ)}, reduced l₁ →
  reduced l₂ → mul_aux l₁ l₂ = reduce (l₁ ++ l₂)
| []      l₂ _  h  := by simp [reduce, mul_aux, reduce_eq_self_of_reduced h]
| (a::l₁) l₂ h₁ h₂ :=
  by rw [mul_aux, mul_aux_eq_reduce_append (reduced_of_reduced_cons h₁) h₂,
    reduce_cons_reduce_eq_reduce_cons (h₁.2 a (mem_cons_self _ _)), cons_append]

lemma reduce_cons_append : ∀ {a b : α × ℤ} {l₁ l₂ : list (α × ℤ)},
  reduce_cons a ((b::l₁) ++ l₂) = reduce_cons a (b::l₁) ++ l₂
| a b [] l₂ := begin
  simp [reduce_cons], split_ifs; simp
end
| a b (c::l₁) l₂ := begin
  rw [cons_append, reduce_cons],
  dsimp,
  split_ifs,
  { simp [reduce_cons, *] },
  { simp [reduce_cons, *] },
  { simp [reduce_cons, *] }
end

lemma mul_aux_reduce_cons : ∀ (a : α) (i : ℤ) (hi : i ≠ 0), ∀ l₁ l₂ : list (α × ℤ),
  reduced l₁ → reduced l₂ → mul_aux (reduce_cons (a, i) l₁) l₂ =
  reduce_cons (a, i) (mul_aux l₁ l₂)
| a i hi []      l₂ h₁ h₂ := rfl
| a i hi ((b, j)::l₁) l₂ h₁ h₂ := begin
  conv_rhs {  },
  rw [mul_aux, reduce_cons_eq_reduce_cons (show (a, i).snd ≠ 0, from hi) h₁,
    reduce_cons_eq_reduce_cons, ← mul_aux_reduce_cons],

end

-- lemma mul_aux_assoc {l₁ l₂ l₃ : list (α × ℤ)} (h₁ : reduced l₁) (h₂ : reduced l₂) (h₃ : reduced l₃) :
--   mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃) :=
-- begin
--   rw [mul_aux_eq_reduce_append (mul_aux_reduced h₁ h₂) h₃,
--     mul_aux_eq_reduce_append h₁ h₂],

-- end

instance : has_mul (free_group α) :=
⟨λ a b : free_group α, ⟨mul_aux a.1 b.1, mul_aux_reduced a.2 b.2⟩⟩

lemma reduce_cons_reduce_cons {a : α} {i j : ℤ} : ∀ {l : list (α × ℤ)},
  i + j = 0 → reduce_cons (a, i) (reduce_cons (a, j) l) = l
| []            hij := by simp [reduce_cons, hij]
| [(c, k)] hij := begin  simp [reduce_cons], split_ifs;
  simp [reduce_cons, add_comm j, add_eq_zero_iff_eq_neg, *] at *,
 end

lemma reduce_cons_reduce_cons {a b : α} {i j : ℤ} : ∀ {l : list (α × ℤ)},
  reduced l → i ≠ 0 → j ≠ 0 → reduce_cons (a, i) (reduce_cons (b, j) l) =
  if a = b
    then if i + j = 0
      then l
      else reduce_cons (a, i + j) l
    else (a, i) :: reduce_cons (b, j)
| []       hl hi hj := begin
  split_ifs,
  simp [reduce_cons, *],
  simp,
end


lemma mul_aux_reduce_cons (a : α) (i : ℤ) : ∀ l₁ l₂ : list (α × ℤ),
  reduced l₁ → reduced l₂ → mul_aux (reduce_cons (a, i) l₁) l₂ =
  reduce_cons (a, i) (mul_aux l₁ l₂)
| []        l₂ h₁ h₂:= rfl
| ((b, j) :: l₁) l₂ h₁ h₂ :=
  begin
    rw [mul_aux, reduce_cons],
    dsimp only,
    split_ifs,
    sorry,

  end
| [(b, j)]       [] h₁ h₂ := begin
    simp [mul_aux, reduce_cons],
    split_ifs,
    { refl },
    { refl },
    { simp [mul_aux, reduce_cons, h] }
  end
|
| [(b, j)] [(c, k)] ⟨h₁c, h₁0⟩ ⟨h₂c, h₂0⟩ := begin
    simp [mul_aux, reduce_cons],
    split_ifs,
    { simp [mul_aux, reduce_cons, *], omega },
    { simp [mul_aux, reduce_cons, h],
      split_ifs,
      { have := h₂0 (c, k) (mem_singleton_self _),
        omega },
      {  } }

  end

lemma mul_aux_assoc (l₁ l₂ l₃ : list (α × ℤ)) (h₁ : reduced l₁) (h₂ : reduced l₂) (h₃ : reduced l₃) :
  mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃) :=
begin
  repeat { rw mul_aux_eq_reduce_append },
  rw [reduce_reduce_append_eq_reduce_append]
,
end

lemma mul_aux_assoc : ∀ (l₁ l₂ l₃ : list (α × ℤ)),
  mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃)
| []      l₂ l₃ := rfl
| (a::l₁) l₂ l₃ := begin
  simp [mul_aux],

end


def inv_aux (l : list (α × ℤ)) : list (α × ℤ) :=
l.reverse.map (λ a, (a.1, -a.2))

lemma reduced_inv_aux {l : list (α × ℤ)} (ha : reduced l) : reduced (inv_aux l) :=
⟨(list.chain'_map _).2 (list.chain'_reverse.2 begin
  convert ha, simp [function.funext_iff, eq_comm]
end), begin simp [inv_aux, eq_comm] , end⟩

-- instance : has_inv (free_group α) :=
-- ⟨λ a, ⟨inv_aux a.1, reduced_inv_aux a.2⟩⟩

-- lemma mul_aux_assoc : ∀ l₁ l₂ l₃ : list (α × ℤ),
--   mul_aux (mul_aux l₁ l₂) l₃ = mul_aux l₁ (mul_aux l₂ l₃)
-- | [] l₂ l₃ := by simp
-- | l₁ [] l₃ := by simp
-- | l₁ l₂ [] := by simp
-- | [(a, i)] [(b, j)] ((c, k) :: l₃) := begin
--   simp with mul_aux,
--   split_ifs; simp [*, add_assoc] with mul_aux at *,
-- end
-- | [(a, i)] ((b, j) :: (c, k) :: l₂) l₃ :=
-- begin
--   simp with mul_aux,
--   split_ifs; simp * with mul_aux
-- end
-- | [(a, i), (b, j)] ((c, k) :: l₂) ((d, l) :: l₃) :=
-- begin
--   simp with mul_aux,
--   split_ifs; simp [*, add_assoc, ← mul_aux_assoc] with mul_aux at *
-- end
-- | ((a, i) :: (b, j) :: (c, k) :: l₁) l₂ l₃ :=
-- begin
--   simp only with mul_aux,
--   rw [← mul_aux_cons_cons, mul_aux_assoc],
--   simp with mul_aux
-- end

-- lemma mul_aux_inv_aux_cancel : ∀ l₁ : list (α × ℤ),
--   mul_aux l₁ (inv_aux l₁) = []
-- | []       := rfl
-- | [(a, i)] := by simp [inv_aux] with mul_aux
-- | ((a, i) :: (b, j) :: l) := begin
--   rw [inv_aux, list.reverse_cons, list.reverse_cons, list.map_append,
--     list.map_append, list.map_singleton, list.map_singleton,
--     mul_aux_cons_cons],

-- end





end free_group
