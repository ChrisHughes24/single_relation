import .approach2_ref

open group_rel
open group_rel.free_group

lemma eval_eval_eq_one {G : Type*} [group G] (atoms : list G)
  (c : certificate atoms) : free_group.eval atoms (c.eval atoms) = 1 :=
begin
  induction c with _ _ hrel _ ih,
  { simp [certificate.eval, eval_one] },
  { simp [certificate.eval, eval_ap, ih, hrel, eval_inv_core, eval_one] }
end

lemma eq_one_of_cert_eval_eq_one {G : Type*} [group G] (atoms : list G) (w : free_group)
  (c : certificate atoms)
  (hrel : eqv (c.eval atoms) w): free_group.eval atoms w = 1 :=
by rw [← eval_eq_of_eqv atoms hrel, eval_eval_eq_one]

@[derive decidable_eq] structure proof_step : Type :=
(conj : free_group)
(rel : free_group)
(rel_index : ℕ)
(rel_is_inv : bool)

def conj (c : free_group) : list proof_step → list proof_step
| [] := []
| (⟨c', r, i, b⟩::l) := ⟨c * c', r, i, b⟩::l

meta def golf₁ :
  list proof_step →
  list proof_step
| []  := []
| [x] := [x]
| (⟨c₁, r₁, i₁, b₁⟩ :: ⟨c₂, r₂, i₂, b₂⟩ :: l) :=
  if c₂ = 1 ∧ r₁ = r₂⁻¹
    then golf₁ (conj c₁ l)
    else let c' := c₁ * r₁ * c₂ in if c' < c₁
      then ⟨c', r₂, i₂, b₂⟩ :: golf₁ (⟨c₂⁻¹ * r₁⁻¹, r₁, i₁, b₁⟩::conj c₂ l)
      else let c₁' := c₁ * c₂ in
           let c₂' := r₂⁻¹ * c₂⁻¹ in
        if c₁' < c₁
          then ⟨c₁', r₂, i₂, b₂⟩ :: golf₁ (⟨c₂', r₁, i₁, b₁⟩::conj (c₂* r₂) l)
          else ⟨c₁, r₁, i₁, b₁⟩ :: golf₁ (⟨c₂, r₂, i₂ , b₂⟩::l)

meta def golf₂ :
  list proof_step →
  list proof_step
| []  := []
| (⟨c₁, r₁, i₁, b₁⟩ :: l) :=
  let cr₁ := c₁ * r₁ in
  if cr₁ < c₁
  then golf₂ (⟨cr₁, r₁, i₁, b₁⟩ :: conj (r₁⁻¹) l)
  else ⟨c₁, r₁, i₁, b₁⟩  :: golf₂ l

meta def golf₃ :
  list proof_step →
  list proof_step
| []  := []
| (⟨c₁, r₁, i₁, b₁⟩ :: l) :=
  let cr₁ := c₁ * r₁⁻¹ in
  if cr₁ < c₁
  then golf₂ (⟨cr₁, r₁, i₁, b₁⟩ :: conj r₁ l)
  else ⟨c₁, r₁, i₁, b₁⟩  :: golf₃ l

meta def golf : Π (l : list proof_step), list proof_step :=
λ l, let l' := golf₁ (golf₂ (golf₃ l)) in
if l' = l then l else golf l'

meta def to_list_proof_step (rels : buffer free_group) (rels_inv : buffer free_group) :
  Π (l : list path_step), list proof_step
| []     := []
| (p::l) :=
  let rel := cond p.rel_is_inv
    (rels_inv.read' p.rel_index)
    (rels.read' p.rel_index) in
  let rₜ := rel.take p.rel_letter_index in
  let oₜ := p.old_word.take p.word_start_index in
  let c := cyclically_reduce_conj (oₜ
    * (rel.rotate p.rel_letter_index)⁻¹
    * p.old_word.drop (p.word_start_index)) in
  ⟨oₜ * rₜ⁻¹, rel, p.rel_index, p.rel_is_inv⟩ ::
    conj (rₜ * oₜ⁻¹ * c) (to_list_proof_step l)



-- def golf₄_core_aux (c r : free_group) :
--  free_group →
--   list (free_group × free_group) →
--   list (free_group × free_group) →
--   list (free_group × free_group)
-- | p l             []  := (c, r) :: l
-- | p l₁ ((c₂, r₂)::l₂) :=
--   if r₂ = r⁻¹ ∧ p = c₂⁻¹
--     then _
--     else golf₄_core_aux (p * c₂) ((c₂, r₂)::l₁) l₂
