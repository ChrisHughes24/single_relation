import coprod.pre

variables {ι : Type*} (M : ι → Type*) {G : ι → Type*} {N : Type*}
variables [Π i, monoid (M i)] [Π i, group (G i)] [monoid N]

def coprod : Type* := {l : list (Σ i, M i) // coprod.pre.reduced l}

namespace coprod

open coprod.pre list
variables {M} [decidable_eq ι] [Π i : ι, decidable_eq (M i)] [Π i, decidable_eq (G i)]

instance : has_one (coprod M) := ⟨⟨[], trivial, by simp⟩⟩
instance : has_mul (coprod M) := ⟨λ a b, ⟨pre.mul a.1 b.1, pre.reduced_mul a.2 b.2⟩⟩

instance : monoid (coprod M) :=
{ mul := (*),
  one := 1,
  mul_assoc := λ a b c, subtype.eq $ pre.mul_assoc a.2 b.2 c.2,
  one_mul := λ _, subtype.eq (pre.one_mul _),
  mul_one := λ a, subtype.eq (pre.mul_one a.2) }

instance : has_inv (coprod G) := ⟨λ a, ⟨pre.inv a.1, reduced_inv _ a.2⟩⟩

instance : group (coprod G) :=
{ mul := (*),
  inv := has_inv.inv,
  one := 1,
  mul_left_inv := λ a, subtype.eq (pre.mul_left_inv _),
  ..coprod.monoid }

def of (i : ι) : M i →* coprod M :=
{ to_fun := λ a, ⟨of i a, reduced_of _ _⟩,
  map_one' := subtype.eq $ of_one _,
  map_mul' := λ a b, subtype.eq $ of_mul _ _ _ }

@[simp] lemma cons_eq_of_mul {l : list (Σ i, M i)} (i : Σ i , M i) (h : reduced (i :: l)) :
  @eq (coprod M) ⟨i :: l, h⟩ (of i.1 i.2 * ⟨l, reduced_of_reduced_cons h⟩) :=
begin
  unfold has_mul.mul,
  cases i with i a,
  have ha : a ≠ 1, from h.2 _ (mem_cons_self _ _),
  have hi' : reduced [⟨i, a⟩], from reduced_singleton ha,
  simp [pre.mul, of, mul_aux, pre.of, ha,
    mul_aux_eq_reduce_append hi' (reduced_of_reduced_cons h),
    reduce_eq_self_of_reduced h],
end

@[simp] lemma nil_eq_one : @eq (coprod M) ⟨[], reduced_nil⟩ 1 := rfl

@[simp] lemma append_eq_mul {l₁ l₂ : list (Σ i, M i)} (h : reduced (l₁ ++ l₂)) :
  @eq (coprod M) ⟨l₁ ++ l₂, h⟩ (⟨l₁, reduced_of_reduced_append_left h⟩ *
    ⟨l₂, reduced_of_reduced_append_right h⟩) :=
begin
  induction l₁ with i l₂ ih,
  { simp },
  { rw [cons_append] at h,
    simp [mul_assoc, ih (reduced_of_reduced_cons h)] }
end

@[simp] lemma eta (w : coprod M) : (⟨w.1, w.2⟩ : coprod M) = w := subtype.eta _ _

instance : decidable_eq (coprod M) := subtype.decidable_eq

def lift (f : Π i, M i →* N) : coprod M →* N :=
{ to_fun := λ a, lift f a.1,
  map_one' := rfl,
  map_mul' := λ _ _, lift_mul _ _ _ }

@[simp] lemma lift_of (f : Π i, M i →* N) (i : ι) (a : M i) : lift f (of i a) = f i a := lift_of _ _ _

@[simp] lemma lift_comp_of (f : Π i, M i →* N) (i : ι) : (lift f).comp (of i) = f i :=
monoid_hom.ext (by simp)

def rec_on_aux {C : coprod M → Sort*} : Π (l : list (Σ i, M i)) (hl : reduced l)
  (h1 : C 1)
  (hof : Π i (a : M i), C (of i a))
  (ih : Π (i : ι) (a : M i) (b : coprod M), C (of i a) → C b → C (of i a * b)),
  C ⟨l, hl⟩
| []         hl h1 hof ih := h1
| (⟨i,a⟩::l) hl h1 hof ih := begin
  rw [cons_eq_of_mul],
  exact ih _ _ _ (by convert hof i a; simp [pre.of, hl.2 _ (mem_cons_self _ _)])
    (rec_on_aux _ _ h1 hof ih)
end

@[elab_as_eliminator]
def rec_on {C : coprod M → Sort*} (a : coprod M)
  (h1 : C 1)
  (hof : Π i (a : M i), C (of i a))
  (ih : Π (i : ι) (a : M i) (b : coprod M), C (of i a) → C b → C (of i a * b)) :
  C a :=
by cases a with i a; exact rec_on_aux i a h1 hof ih

lemma hom_ext {f g : coprod M →* N} (h : ∀ i, f.comp (of i) = g.comp (of i)) : f = g :=
begin
  ext g,
  refine coprod.rec_on g _ _ _,
  { simp },
  { intros i a,
    simpa using monoid_hom.ext_iff.1 (h i) a },
  { simp {contextual := tt} }
end

lemma of_mul_cons (i j : ι) (a : M i) (b : M j) (l : list (Σ i, M i))
  (h : reduced (⟨j, b⟩ :: l)) : of i a * ⟨⟨j, b⟩ :: l, h⟩ =
  if ha1 : a = 1 then ⟨⟨j, b⟩ :: l, h⟩
    else if hij : i = j
      then if hab : a * cast (congr_arg M hij).symm b = 1
        then ⟨l, reduced_of_reduced_cons h⟩
        else ⟨⟨i, a * cast (congr_arg M hij).symm b⟩ :: l,
          reduced_cons_of_reduced_cons
            (show reduced (⟨i, cast (congr_arg M hij).symm b⟩ :: l),
              by subst hij; simpa) hab⟩
      else ⟨⟨i, a⟩ :: ⟨j, b⟩ :: l, reduced_cons_cons hij ha1 h⟩ :=
show (show coprod M, from ⟨pre.mul_aux _ _, _⟩) = _, begin
  simp [of, pre.of],
  split_ifs; simp [mul_aux, of, pre.of];
  split_ifs; simp [reverse_core_eq];
  split_ifs; simp [mul_assoc, of, pre.of]
end

def to_list : coprod M → list (Σ i, M i) := subtype.val

@[simp] lemma to_list_one : (1 : coprod M).to_list = [] := rfl

lemma to_list_of (i : ι) (a : M i) : (of i a).to_list =
  if a = 1 then [] else [⟨i, a⟩] := rfl

@[simp] lemma to_list_mk (l : list (Σ i, M i)) (hl : reduced l) :
  @to_list _ M _ _ _ ⟨l, hl⟩ = l := rfl

end coprod
