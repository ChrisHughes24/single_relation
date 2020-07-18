import .inductive_step

variables {ι : Type} [decidable_eq ι]

noncomputable def cyclically_reduce : free_group ι → free_group ι × free_group ι
| ⟨[], _⟩      := (1, 1)
| ⟨[i], h⟩     := (⟨[i], h⟩, 1)
| ⟨i::j::l, h⟩ :=
  let k := (j :: l : list _).last (list.cons_ne_nil _ _) in
  if i.1 = k.1 ∧ int.sign i.2 ≠ int.sign j.2
  then let z := i.2 * k.2 in
    let init : free_group ι := ⟨(j :: l : list _).init, sorry⟩ in
    let w' := cyclically_reduce ⟨(j :: l : list _).init, sorry⟩ in
    (_, ⟨(j::l).init, _⟩)
  else (⟨i::j::l, h⟩, 1)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ x, x.1.length)⟩]}