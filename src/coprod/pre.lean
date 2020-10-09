import data.list.chain
import data.sigma.basic

variables {ι : Type*} {M : ι → Type*} {G : ι → Type*} {N : Type*}
variables [Π i, monoid (M i)] [Π i, group (G i)] [monoid N]

open list function

namespace coprod.pre

def reduced (l : list (Σ i, M i)) : Prop :=
l.chain' (λ a b, a.1 ≠ b.1) ∧ ∀ a : Σ i, M i, a ∈ l → a.2 ≠ 1

@[simp] lemma reduced_nil : reduced ([] : list (Σ i, M i)) :=
⟨list.chain'_nil, λ _, false.elim⟩

lemma reduced_singleton {i : Σ i, M i} (hi : i.2 ≠ 1) : reduced [i] :=
⟨by simp, begin
  cases i with i a,
  rintros ⟨j, b⟩,
  simp only [and_imp, ne.def, mem_singleton],
  rintro rfl h₂,
  simp * at *
end⟩

lemma reduced_of_reduced_cons {i : Σ i, M i} {l : list (Σ i, M i)}
  (h : reduced (i :: l)) : reduced l :=
⟨(list.chain'_cons'.1 h.1).2, λ b hb, h.2 _ (mem_cons_of_mem _ hb)⟩

lemma reduced_cons_of_reduced_cons {i : ι} {a b : M i} {l : list (Σ i, M i)}
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

lemma reduced_cons_cons {i j : ι} {a : M i} {b : M j}
  {l : list (Σ i, M i)} (hij : i ≠ j) (ha : a ≠ 1)
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

lemma reduced_reverse {l : list (Σ i, M i)} (h : reduced l) : reduced l.reverse :=
⟨chain'_reverse.2 $ by {convert h.1, simp [function.funext_iff, eq_comm] },
  by simpa using h.2⟩

@[simp] lemma reduced_reverse_iff {l : list (Σ i, M i)} : reduced l.reverse ↔ reduced l :=
⟨λ h, by convert reduced_reverse h; simp, reduced_reverse⟩

lemma reduced_of_reduced_append_right : ∀ {l₁ l₂ : list (Σ i, M i)} (h : reduced (l₁ ++ l₂)),
  reduced l₂
| []      l₂ h := h
| (i::l₁) l₂ h := begin
  rw cons_append at h,
  exact reduced_of_reduced_append_right (reduced_of_reduced_cons h)
end

lemma reduced_of_reduced_append_left {l₁ l₂ : list (Σ i, M i)} (h : reduced (l₁ ++ l₂)) :
  reduced l₁ :=
begin
  rw [← reduced_reverse_iff],
  rw [← reduced_reverse_iff, reverse_append] at h,
  exact reduced_of_reduced_append_right h
end

variables {ι} [decidable_eq ι] {M} [Π i, decidable_eq (M i)]

def rcons : (Σ i, M i) → list (Σ i, M i) → list (Σ i, M i)
| i []     := [i]
| i (j::l) :=
  if hij : i.1 = j.1
    then let c := i.2 * cast (congr_arg M hij).symm j.2 in
      if c = 1
        then l
        else ⟨i.1, c⟩ :: l
    else i::j::l

def reduce : list (Σ i, M i) → list (Σ i, M i)
| []       := []
| (i :: l) := if i.2 = 1 then reduce l else rcons i (reduce l)

@[simp] lemma reduce_nil : reduce ([] : list (Σ i, M i)) = [] := rfl

lemma reduce_cons (i : Σ i, M i) (l : list (Σ i, M i)) :
  reduce (i::l) = if i.2 = 1 then reduce l else rcons i (reduce l) := rfl

lemma reduced_rcons : ∀ {i : Σ i, M i} {l : list (Σ i, M i)},
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

lemma reduced_reduce : ∀ l : list (Σ i, M i), reduced (reduce l)
| []     := reduced_nil
| (a::l) := begin
  rw reduce,
  split_ifs,
  { exact reduced_reduce l },
  { exact reduced_rcons h (reduced_reduce l) }
end

lemma rcons_eq_cons : ∀ {i : Σ i, M i} {l : list (Σ i, M i)},
  reduced (i :: l) → rcons i l = i :: l
| i []     h := rfl
| i (j::l) h := dif_neg (chain'_cons.1 h.1).1

lemma rcons_reduce_eq_reduce_cons : ∀ {i : Σ i, M i} {l : list (Σ i, M i)},
  i.2 ≠ 1 → rcons i (reduce l) = reduce (i :: l)
| a []     ha := by simp [rcons, reduce, ha]
| a (b::l) ha := begin
  rw [reduce],
  split_ifs,
  { rw [reduce, if_neg ha, reduce, if_pos h] },
  { rw [reduce, if_neg ha, reduce, if_neg h] }
end

lemma reduce_eq_self_of_reduced : ∀ {l : list (Σ i, M i)}, reduced l → reduce l = l
| []     h := rfl
| (a::l) h := by rw [← rcons_reduce_eq_reduce_cons (h.2 a (mem_cons_self _ _)),
    reduce_eq_self_of_reduced (reduced_of_reduced_cons h), rcons_eq_cons h]

lemma rcons_eq_reduce_cons {i : Σ i, M i} {l : list (Σ i, M i)}
  (ha : i.2 ≠ 1) (hl : reduced l) : rcons i l = reduce (i :: l) :=
by rw [← rcons_reduce_eq_reduce_cons ha, reduce_eq_self_of_reduced hl]

@[simp] lemma reduce_reduce (l : list (Σ i, M i)) : reduce (reduce l) = reduce l :=
reduce_eq_self_of_reduced (reduced_reduce l)

@[simp] lemma reduce_cons_reduce_eq_reduce_cons (i : Σ i, M i) (l : list (Σ i, M i)) :
  reduce (i :: reduce l) = reduce (i :: l)  :=
if ha : i.2 = 1 then by rw [reduce, if_pos ha, reduce, if_pos ha, reduce_reduce]
else by rw [← rcons_reduce_eq_reduce_cons ha, ← rcons_reduce_eq_reduce_cons ha,
    reduce_reduce]

lemma length_rcons_le : ∀ (i : Σ i, M i) (l : list (Σ i, M i)),
  (rcons i l).length ≤ (i::l : list _).length
| i      []          := le_refl _
| ⟨i, a⟩ (⟨j, b⟩::l) := begin
  simp [rcons],
  split_ifs,
  { repeat { constructor } },
  { simp },
  { simp }
end

lemma length_reduce_le : ∀ (l : list (Σ i, M i)),
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

lemma length_rcons_lt_or_eq_rcons : ∀ (i : Σ i, M i) (l : list (Σ i, M i)),
  (rcons i l).length < (i :: l : list _).length ∨ rcons i l = (i::l)
| i [] := or.inr rfl
| i (j::l) := begin
  simp only [rcons],
  split_ifs,
  { exact or.inl (nat.lt_succ_of_le (nat.le_succ _)) },
  { exact or.inl (nat.lt_succ_self _) },
  { simp }
end

lemma length_reduce_lt_or_eq_reduce : ∀ (l : list (Σ i, M i)),
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

lemma rcons_append : ∀ {i j : Σ i, M i} {l₁ l₂ : list (Σ i, M i)},
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

lemma rcons_rcons_of_mul_eq_one {i : ι} {a b : M i} : ∀ {l : list (Σ i, M i)},
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

lemma rcons_rcons_of_mul_ne_one {i : ι} {a b : M i} : ∀ {l : list (Σ i, M i)},
  a * b ≠ 1 → a ≠ 1 → reduced l → rcons ⟨i, a⟩ (rcons ⟨i, b⟩ l) = rcons ⟨i, a * b⟩ l
| []          hab ha hl := by simp [rcons, hab]
| [⟨j, c⟩]    hab ha hl := begin
  simp only [rcons],
  split_ifs,
  { rw [mul_assoc, h_1, mul_one] at h_2,
    exact (ha h_2).elim },
  { simp [rcons, mul_assoc, h_1] },
  { simp only [rcons, ← mul_assoc, *, dif_pos rfl, if_pos rfl, cast_eq] },
  { dsimp only at h,
    subst h,
    simp only [rcons, dif_pos rfl, ← mul_assoc, cast_eq, *] at *,
    simp, },
  { simp [rcons, if_neg hab, if_pos rfl] }
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
  { simp [*, rcons, ← mul_assoc] at * },
  { simp [*, rcons, ← mul_assoc] },
  { simp [*, rcons] }
end

lemma reduce_rcons : ∀ {i : Σ i, M i} (l : list (Σ i, M i)), i.2 ≠ 1 →
  reduce (rcons i l) = rcons i (reduce l)
| i []               hi := by simp [rcons, reduce, hi]
| ⟨i, a⟩ [⟨j, b⟩]    ha := begin
    replace ha : a ≠ 1 := ha,
    dsimp only [reduce, rcons],
    by_cases hij : i = j,
    { subst hij,
      split_ifs;
      simp [*, reduce, rcons] at * },
    { simp [hij, reduce, rcons, ha] }
  end
| ⟨i, a⟩ (⟨j, b⟩::l) ha := begin
  dsimp only [rcons],
  split_ifs,
  { subst h,
    rw [cast_eq] at h_1,
    rw [reduce, if_neg, rcons_rcons_of_mul_eq_one h_1 (reduced_reduce _)],
    { refine λ hb : b = 1, _,
      rw [hb, mul_one] at h_1,
      exact ha h_1 } },
  { subst h,
    rw [reduce, if_neg h_1, reduce],
    split_ifs,
    { erw [cast_eq, show b = 1, from h, mul_one] },
    { rw cast_eq at h_1,
      rw [rcons_rcons_of_mul_ne_one h_1 ha (reduced_reduce l), cast_eq], } },
  { rw [rcons_eq_reduce_cons ha (reduced_reduce _), reduce_cons_reduce_eq_reduce_cons] }
end

lemma reduce_cons_cons_of_mul_eq_one {l : list (Σ i, M i)} {i : ι} {a b : M i}
  (ha : a ≠ 1) (hb : b ≠ 1) (hab : a * b = 1) : reduce (⟨i, a⟩ :: ⟨i, b⟩ :: l) = reduce l :=
by rw [reduce, if_neg ha, reduce, if_neg hb, rcons_rcons_of_mul_eq_one hab (reduced_reduce _)]

lemma reduce_cons_cons_of_mul_ne_one {l : list (Σ i, M i)} {i : ι} {a b : M i}
  (ha : a ≠ 1) (hab : a * b ≠ 1) : reduce (⟨i, a⟩ :: ⟨i, b⟩ :: l) = reduce (⟨i, a * b⟩ :: l) :=
begin
  rw [reduce, if_neg ha, reduce],
  split_ifs,
  { rw [rcons_eq_reduce_cons (show (⟨i, a⟩ : Σ i, M i).snd ≠ 1, from ha) (reduced_reduce _),
      show b = 1, from h, mul_one, reduce_cons_reduce_eq_reduce_cons] },
  { rw [rcons_rcons_of_mul_ne_one hab ha (reduced_reduce _),
      rcons_eq_reduce_cons (show (⟨i, a * b⟩ : Σ i, M i).snd ≠ 1, from hab : _) (reduced_reduce _),
      reduce_cons_reduce_eq_reduce_cons] }
end

@[simp] lemma reduce_reduce_append_eq_reduce_append : ∀ (l₁ l₂ : list (Σ i, M i)),
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

@[simp] lemma reduce_append_reduce_eq_reduce_append : ∀ (l₁ l₂ : list (Σ i, M i)),
  reduce (l₁ ++ reduce l₂) = reduce (l₁ ++ l₂)
| []      l₂ := by simp
| (a::l₁) l₂ := by rw [cons_append, ← reduce_cons_reduce_eq_reduce_cons,
    reduce_append_reduce_eq_reduce_append,
    reduce_cons_reduce_eq_reduce_cons, cons_append]

lemma reduced_iff_reduce_eq_self {l : list (Σ i, M i)} :
  reduced l ↔ reduce l = l :=
⟨reduce_eq_self_of_reduced, λ h, h ▸ reduced_reduce l⟩

lemma reduced_append_overlap {l₁ l₂ l₃ : list (Σ i, M i)}
  (h₁ : reduced (l₁ ++ l₂)) (h₂ : reduced (l₂ ++ l₃)) (hn : l₂ ≠ []):
  reduced (l₁ ++ l₂ ++ l₃) :=
⟨chain'.append_overlap h₁.1 h₂.1 hn,
  λ i hi, (mem_append.1 hi).elim (h₁.2 _) (λ hi, h₂.2 _ (mem_append_right _ hi))⟩

/-- `mul_aux` returns `reduce (l₁.reverse ++ l₂)` -/
def mul_aux : Π (l₁ l₂ : list (Σ i, M i)), list (Σ i, M i)
| []      l₂      := l₂
| (i::l₁) []      := reverse (i :: l₁)
| (i::l₁) (j::l₂) :=
  if hij : i.1 = j.1
    then let c := i.2 * cast (congr_arg M hij).symm j.2 in
      if c = 1
        then mul_aux l₁ l₂
        else l₁.reverse_core (⟨i.1, c⟩::l₂)
    else l₁.reverse_core (i::j::l₂)

@[simp] lemma mul_aux_nil (l : list (Σ i, M i)) : mul_aux l [] = l.reverse :=
by cases l; refl

lemma mul_aux_eq_reduce_append : ∀ {l₁ l₂: list (Σ i, M i)},
  reduced l₁ → reduced l₂ → mul_aux l₁ l₂ = reduce (l₁.reverse ++ l₂)
| []          l₂          := λ h₁ h₂,
  by clear_aux_decl; simp [mul_aux, reduce_eq_self_of_reduced, *]
| (i::hd)     []          := λ h₁ h₂,
  by rw [mul_aux, append_nil, reduce_eq_self_of_reduced (reduced_reverse h₁)]
| (⟨i,a⟩::l₁) (⟨j,b⟩::l₂) := λ h₁ h₂,
  begin
    simp only [mul_aux],
    dsimp only,
    have ha : a ≠ 1, from h₁.2 ⟨i, a⟩ (by simp),
    have hb : b ≠ 1, from h₂.2 ⟨j, b⟩ (list.mem_cons_self _ _),
    rcases decidable.em (i = j) with ⟨rfl, hij⟩,
    { rw [dif_pos rfl, cast_eq],
      split_ifs,
      { have hrl₁ : reduced l₁,
        { exact reduced_of_reduced_cons h₁ },
        have hrl₂ : reduced l₂, from reduced_of_reduced_cons h₂,
        rw [mul_aux_eq_reduce_append hrl₁ hrl₂, reverse_cons, append_assoc,
          cons_append, nil_append, ← reduce_append_reduce_eq_reduce_append _ (_ :: _),
          reduce_cons_cons_of_mul_eq_one ha hb h_1,
          reduce_append_reduce_eq_reduce_append] },
      { have hrl₁ :reduced (l₁.reverse ++ [⟨i, a * b⟩]),
        { rw [← reduced_reverse_iff, reverse_append, reverse_reverse,
            reverse_singleton, singleton_append],
          exact reduced_cons_of_reduced_cons h₁ h_1 },
        have hrl₂ :reduced ([⟨i, a * b⟩] ++ l₂),
        { rw [singleton_append],
          exact reduced_cons_of_reduced_cons h₂ h_1 },
        simp only [reverse_cons, singleton_append, append_assoc, reverse_core_eq],
        rw [← reduce_append_reduce_eq_reduce_append,
          reduce_cons_cons_of_mul_ne_one ha h_1,
          reduce_append_reduce_eq_reduce_append, ← singleton_append, ← append_assoc],
        exact (reduce_eq_self_of_reduced
          (reduced_append_overlap hrl₁ hrl₂ (by simp))).symm } },
    { suffices : reduce (l₁.reverse ++ [⟨i, a⟩, ⟨j, b⟩] ++ l₂) =
        l₁.reverse ++ [⟨i, a⟩, ⟨j, b⟩] ++ l₂,
      { simpa [eq_comm, dif_neg h, reverse_core_eq] },
      have hrl₁ : reduced (l₁.reverse ++ [⟨i, a⟩, ⟨j, b⟩]),
      { rw [← reduced_reverse_iff],
        simp only [reverse_append, reverse_cons, cons_append, reverse_nil, nil_append,
          reverse_reverse],
        refine reduced_cons_cons (ne.symm h) hb h₁ },
      have hrl₂ : reduced ([⟨i, a⟩, ⟨j, b⟩] ++ l₂),
      { simp only [cons_append, nil_append],
        refine reduced_cons_cons h ha h₂ },
      exact reduce_eq_self_of_reduced (reduced_append_overlap hrl₁ hrl₂ (by simp)) }
  end

protected def mul (l₁ l₂ : list (Σ i, M i)) : list (Σ i, M i) :=
mul_aux l₁.reverse l₂

lemma mul_eq_reduce_append {l₁ l₂ : list (Σ i, M i)} (h₁ : reduced l₁) (h₂ : reduced l₂) :
  coprod.pre.mul l₁ l₂ = reduce (l₁ ++ l₂) :=
by rw [coprod.pre.mul, mul_aux_eq_reduce_append (reduced_reverse h₁) h₂, reverse_reverse]

lemma reduced_mul {l₁ l₂ : list (Σ i, M i)} (h₁ : reduced l₁) (h₂ : reduced l₂) :
  reduced (coprod.pre.mul l₁ l₂) :=
(mul_eq_reduce_append h₁ h₂).symm ▸ reduced_reduce _

protected lemma mul_assoc {l₁ l₂ l₃ : list (Σ i, M i)} (h₁ : reduced l₁) (h₂ : reduced l₂)
  (h₃ : reduced l₃) : pre.mul (pre.mul l₁ l₂) l₃ = pre.mul l₁ (pre.mul l₂ l₃) :=
begin
  rw [mul_eq_reduce_append (reduced_mul h₁ h₂) h₃, mul_eq_reduce_append h₁ h₂,
    mul_eq_reduce_append h₂ h₃, mul_eq_reduce_append h₁ (reduced_reduce _)],
  simp [append_assoc]
end

protected lemma one_mul (l : list (Σ i, M i)) : pre.mul [] l = l := rfl

protected lemma mul_one {l : list (Σ i, M i)} (h : reduced l) : pre.mul l [] = l :=
by rw [mul_eq_reduce_append h reduced_nil, append_nil, reduce_eq_self_of_reduced h]

section lift

variable (f : Π i, M i →* N)

def lift (l : list (Σ i, M i)) : N :=
l.foldl (λ n i, n * f i.1 i.2) 1

lemma lift_eq_map_prod (l : list (Σ i, M i)) :
  lift f l = (l.map (λ i : Σ i, M i, f i.1 i.2)).prod :=
begin
  rw [lift, ← one_mul (l.map _).prod],
  generalize h : (1 : N) = n, clear h,
  induction l with i l ih generalizing n,
  { simp },
  { rw [foldl_cons, ih, map_cons, prod_cons, mul_assoc] }
end

lemma map_prod_mul_aux : ∀ (l₁ l₂ : list (Σ i, M i)),
  ((mul_aux l₁ l₂).map (λ i : Σ i, M i, f i.1 i.2)).prod =
  (l₁.reverse.map (λ i : Σ i, M i, f i.1 i.2)).prod *
  (l₂.map (λ i : Σ i, M i, f i.1 i.2)).prod
| []      l₂      := by simp [mul_aux]
| (i::l₁) []      := by simp [mul_aux]
| (⟨i,a⟩::l₁) (⟨j,b⟩::l₂) := begin
  rw [mul_aux],
  split_ifs,
  { dsimp only at h,
    subst h,
    rw [cast_eq] at h_1,
    simp only [prod_nil, mul_one, reverse_cons, map, prod_cons, prod_append,
        map_append, map_reverse, mul_assoc],
    rw [← mul_assoc (f _ _), ← monoid_hom.map_mul, h_1],
    simp [map_prod_mul_aux] },
  { dsimp only at h,
    subst h,
    simp [reverse_core_eq, mul_assoc] },
  { simp [reverse_core_eq, mul_assoc] }
end

lemma lift_mul (l₁ l₂ : list (Σ i, M i)) : lift f (pre.mul l₁ l₂) = lift f l₁ * lift f l₂ :=
by simp [pre.mul, lift_eq_map_prod, map_prod_mul_aux]

end lift

section of
variables (i : ι) (a b : M i)

def of (i : ι) (a : M i) : list (Σ i, M i) :=
if a = 1 then [] else [⟨i, a⟩]

lemma reduced_of (i : ι) (a : M i) : reduced (of i a) :=
begin
  rw of,
  split_ifs,
  { simp },
  { exact reduced_singleton h }
end

lemma of_one : of i (1 : M i) = [] := if_pos rfl

lemma of_mul : of i (a * b) = pre.mul (of i a) (of i b) :=
begin
  simp only [of, pre.mul, mul_aux],
  split_ifs; simp [mul_aux, *, reverse_core_eq] at *
end

lemma lift_of (f : Π i, M i →* N) : lift f (of i a) = f i a :=
begin
  simp [lift, of],
  split_ifs;
  simp *
end

end of

section embedding
variables {κ : Type*} {O : κ → Type*} [Π i, monoid (O i)]
variables (f : ι → κ) (hf : injective f)
  (g : Π i, M i →* O (f i)) (hg : ∀ i a, g i a = 1 → a = 1)

protected def embedding (l : list (Σ i, M i)) : list Σ i, O i :=
l.map (λ i, ⟨f i.1, g i.1 i.2⟩)

include hf hg

variables [decidable_eq κ] [Π i, decidable_eq (O i)]

lemma embedding_mul_aux : ∀ (l₁ l₂ : list (Σ i, M i)),
  pre.embedding f g (mul_aux l₁ l₂) = mul_aux (pre.embedding f g l₁) (pre.embedding f g l₂)
| []      l₂      := rfl
| (i::l₁) []      := by simp [pre.embedding, mul_aux]
| (⟨i,a⟩::l₁) (⟨j, b⟩::l₂) :=
  begin
    rw [mul_aux],
    split_ifs,
    { dsimp only at h,
      subst h,
      have : g i a * g i b = 1,
      { erw [← monoid_hom.map_mul, h_1, monoid_hom.map_one] },
      rw [embedding_mul_aux],
      simp [pre.embedding, mul_aux, this] },
    { dsimp only at h,
      subst h,
      have : g i a * g i b ≠ 1,
      { rw [← monoid_hom.map_mul],
        exact mt (hg i (a * b)) h_1 },
      simp [pre.embedding, mul_aux, this, reverse_core_eq] },
    { dsimp only at h,
      simp [pre.embedding, mul_aux, reverse_core_eq, hf.eq_iff, h] }
  end

lemma embedding_mul {l₁ l₂ : list (Σ i, M i)} :
  pre.embedding f g (pre.mul l₁ l₂) = pre.mul (pre.embedding f g l₁) (pre.embedding f g l₂) :=
begin
  simp [pre.mul, embedding_mul_aux _ hf _ hg],
  simp [pre.embedding]
end

lemma reduced_embedding {l : list (Σ i, M i)} (hl : reduced l) :
  reduced (pre.embedding f g l) :=
⟨by simp [pre.embedding, list.chain'_map, hf.eq_iff, hl.1],
  begin
    simp only [pre.embedding, mem_map, and_imp, sigma.forall],
    rintros i a ⟨⟨j, b⟩, hjb, rfl, h⟩,
    rw [heq_iff_eq] at h,
    subst a,
    exact mt (hg j b) (hl.2 _ hjb)
  end⟩

end embedding

section inv

variable [Π i, decidable_eq (G i)]

protected def inv (l : list (Σ i, G i)) : list (Σ i, G i) :=
list.reverse (l.map (λ i : Σ i, G i, ⟨i.1, i.2⁻¹⟩))

lemma reduced_inv (l : list (Σ i, G i)) (hl : reduced l) :
  reduced (pre.inv l) :=
⟨list.chain'_reverse.2 ((list.chain'_map _).2 $
  by { convert hl.1, simp [function.funext_iff, eq_comm, flip] }),
begin
  rintros ⟨i, a⟩ hi,
  rw [pre.inv, mem_reverse, mem_map] at hi,
  rcases hi with ⟨⟨j, b⟩, hjl, h⟩,
  simp only at h,
  cases h with hij hba,
  subst hij,
  convert inv_ne_one.2 (hl.2 ⟨j, b⟩ hjl),
  simp * at *
end⟩

protected lemma mul_left_inv_aux : ∀ l : list (Σ i, G i),
  mul_aux (l.map (λ i : Σ i, G i, ⟨i.1, i.2⁻¹⟩)) l = []
| []     := rfl
| (i::l) := by simp [mul_aux, mul_left_inv_aux l]

protected lemma mul_left_inv (l : list (Σ i, G i)) :
  pre.mul (pre.inv l) l = [] :=
by rw [pre.mul, pre.inv, reverse_reverse, pre.mul_left_inv_aux]

end inv

end coprod.pre