import .base_case tactic

open free_group multiplicative

variables {ι : Type} [decidable_eq ι]

def golf_single_aux (r : free_group ι) : Π (w : free_group ι) (wl : ℕ), free_group ι
| w wl :=
  let wr := w * r in
  let wrl := wr.to_list.length in
  if h : wrl < wl
    then golf_single_aux wr wrl
    else w
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩] }

/-- Returns the shortest word of the form `w * r^n` with `n ∈ ℤ` -/
def golf_single (r : free_group ι) (w : free_group ι) : free_group ι :=
let wr := w * r in
let wrl := wr.to_list.length in
let wl := w.to_list.length in
if wrl < wl
  then golf_single_aux r wr wrl
  else
    let rn := r⁻¹ in
    let wrn := w * rn in
    let wrnl := wrn.to_list.length in
    if wrnl < wl
      then golf_single_aux rn wrn wrnl
      else w

#eval golf_single (of "a") (of "a")

def golf_right (r : free_group ι) : Π (w : free_group ι) (wl : ℕ), free_group ι × ℕ
| w wl :=
  let rw := r * w in
  let rwl := rw.to_list.length in
  if h : rwl < wl
    then let g := golf_right rw rwl in (g.1, g.2 + 1)
    else (rw, 0)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩] }

def golf_aux (r : free_group ι) : free_group (free_group ι) →
  free_group (free_group ι) × bool
| ⟨[], _⟩        := (1, ff)
| ⟨[i], _⟩       := (⟨[i], sorry⟩, ff)
| ⟨(i::j::l), _⟩ :=
  let ε : ℤ := int.sign (to_add i.2) in
  let iri := (mul_aut.conj i.1) (r ^ ε) in
  let (g, n) := golf_right iri j.1 j.1.to_list.length in
  let gl := golf_right (of' j.1 j.2 * ⟨l, sorry⟩) in
  golf_aux (of' i.1 (i.2 * of_add (ε * n)))
using_well_founded { dec_tac := sorry }