import initial
import P
import order.lexicographic

open free_group multiplicative semidirect_product

variables {ι : Type} [decidable_eq ι] [has_lt ι] [decidable_rel ((<) : ι → ι → Prop)]

def lex_length : Π (w₁ w₂ : free_group ι), Prop :=
λ w₁ w₂, prod.lex
  (<)
  (list.lex (λ i₁ i₂ : Σ i : ι, C∞, prod.lex (<) (<)
    (i₁.2.to_add.nat_abs, i₁.1)
    (i₂.2.to_add.nat_abs, i₂.1)))
  (w₁.to_list.length, w₁.to_list)
  (w₂.to_list.length, w₂.to_list)

instance lex_length_decidable : decidable_rel (@lex_length ι _ _ _) :=
by dunfold lex_length; apply_instance

meta def golf_single_aux (r : free_group ι) : Π (w : free_group ι), free_group ι
| w :=
  let wr := w * r in
  if h : lex_length wr w
    then golf_single_aux wr
    else w
-- using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩] }

/-- Returns the shortest word of the form `w * r^n` with `n ∈ ℤ` -/
meta def golf_single (r : free_group ι) (w : free_group ι) : free_group ι :=
let wr := w * r in
-- let wrl := wr.to_list.length in
-- let wl := w.to_list.length in
if lex_length wr w
  then golf_single_aux r wr
  else
    let rn := r⁻¹ in
    let wrn := w * rn in
    -- let wrnl := wrn.to_list.length in
    if lex_length wrn w
      then golf_single_aux rn wrn
      else w

meta def golf₁ (r : free_group ι) (p : P (free_group ι)) : P (free_group ι) :=
⟨free_group.map (golf_single r) p.left, p.right⟩

/-- Returns the shortest word of the form `r^n * w` with `n ∈ ℕ` -/
meta def golf_right (r : free_group ι) (max : ℕ) : Π (w : free_group ι), free_group ι × ℕ
| w :=
  let rw := r * w in
  if h : lex_length rw w
    then let g := golf_right rw in if g.2 < max then (g.1, g.2 + 1) else (rw, g.2)
    else (w, 0)

meta def golf₂_core (r : free_group ι) : Π (p₁ p₂ : free_group (free_group ι)),
  free_group (free_group ι)
| ⟨[], _⟩     ⟨p₂, _⟩       := of_list p₂
| ⟨(w::l), _⟩ ⟨[], _⟩       := golf₂_core (of_list l) (of_list [w])
| ⟨(⟨w₁,a⟩::l₁), _⟩ ⟨(⟨w₂,b⟩::l₂), _⟩ :=
  if w₁ = w₂
    then if a * b = 1
      then golf₂_core (of_list l₁) (of_list l₂)
      else golf₂_core (of_list l₁) (of_list (⟨w₁, a * b⟩ :: l₂))
    else
      let ε := (to_add a).sign in
      let w₁rw₁ := w₁ * (r ^ ε) * w₁⁻¹ in
      let (g, n) := golf_right  w₁rw₁ (to_add a).nat_abs w₂ in
      if n ≠ 0
        then
          golf₂_core
            (of_list [⟨w₁, of_add (ε * n)⟩] *
              of_list [⟨g, b⟩] *
              of' w₁ (of_add (to_add a - ε * n)) * of_list l₁)
            (of_list l₂)
        else
          let ε := (to_add b).sign in
          let w₂rw₂ := w₂ * (r ^ (-ε)) * w₂⁻¹ in
          let (g, n) := golf_right w₂rw₂ (to_add b).nat_abs w₁ in
          if n ≠ 0
            then
              golf₂_core
                (of' w₂ (of_add (to_add b - ε * n)) *
                  of_list [⟨g, a⟩] *
                  of_list [⟨w₂, of_add (ε * n)⟩] *
                  of_list l₁)
                (of_list l₂)
            else golf₂_core (of_list l₁) (of_list (⟨w₁, a⟩ :: ⟨w₂, b⟩ :: l₂))

meta def golf₂ (r : free_group ι) (p : P (free_group ι)) : P (free_group ι) :=
⟨golf₂_core r (of_list p.left.to_list.reverse) 1, p.right⟩
