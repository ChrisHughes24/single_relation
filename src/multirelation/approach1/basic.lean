import coprod.free_group tactic initial order.lexicographic

namespace group_rel

open native free_group

@[derive decidable_rel] def lex_length : Π (w₁ w₂ : free_group ℕ), Prop :=
λ w₁ w₂, prod.lex
  (<)
  (list.lex (λ i₁ i₂ : Σ i : ℕ, C∞, prod.lex (<) (<) (i₁.1, i₁.2) (i₂.1, i₂.2)))
  (w₁.length, w₁.to_list)
  (w₂.length, w₂.to_list)

def free_group_lt : has_lt (free_group ℕ) := ⟨lex_length⟩

instance : inhabited (free_group ℕ) := ⟨1⟩

local attribute [instance] free_group_lt

structure path_step : Type :=
(previous_word : free_group ℕ) --previous word
(word₁ : free_group ℕ)
(rel : ℕ)
(inv : bool) -- tt = rel⁻¹, ff = rel
(word₂ : free_group ℕ) -- satisfying word₁ * word₂ = previous word
    -- and word₁ * rel * word₂ = new word

meta def leaves : Type :=
rb_map
  (free_group ℕ) --new word
  (free_group ℕ × option path_step)

meta def seen : Type :=
rb_map (free_group ℕ)
  (free_group ℕ × option path_step)

instance : inhabited path_step := ⟨⟨1, 1, 0, ff, 1⟩⟩
meta instance : inhabited leaves := ⟨mk_rb_map⟩
meta instance : inhabited seen := ⟨mk_rb_map⟩

open  free_group multiplicative

@[derive monad] meta def M : Type → Type :=
except_t unit (state_t (leaves × seen) (reader (buffer (free_group ℕ))))

meta def get_leaves : M leaves :=
except_t.lift $ state_t.get >>= λ x, return x.1

meta def get_seen : M seen :=
except_t.lift $ state_t.get >>= λ x, return x.2

meta def stop : M unit := ⟨return (except.error ())⟩

meta def run (rels : buffer (free_group ℕ)) (word : free_group ℕ) (m : M unit) : leaves × seen :=
let x := reader_t.run (state_t.run m.run (rb_map.of_list [(word, (word, none))], mk_rb_map)) rels in x.snd

meta def add_seen_erase_leaf (word : free_group ℕ) (p : option path_step) : M unit :=
except_t.lift $ state_t.modify (λ x, (x.1.erase word, x.2.insert word (word, p)))

meta def get_rels : M (buffer (free_group ℕ)) :=
except_t.lift $ state_t.lift reader_t.read

meta def get_rel (i : ℕ) (inv : bool) : M (free_group ℕ) :=
except_t.lift $ state_t.lift (reader_t.read >>= λ b, return (cond inv (b.read' i)⁻¹ (b.read' i)))

meta def add_leaf
  (old_word word₁ word₂ : free_group ℕ) -- Should satisfy old_word = word₁ * word₂
  (rel : free_group ℕ)
  (rel_index : ℕ) (inv : bool) : M unit :=
do let word := word₁ * rel * word₂,
if word = 1 then stop
else
do s ← get_seen,
(s.find word).elim
  (except_t.lift $ state_t.modify
    (λ l, (l.1.insert word (word, (some ⟨old_word, word₁, rel_index, inv, word₂⟩)), l.2)))
  (λ _, return ())

meta def add_leaves_of_rel_core
  (old_word : free_group ℕ)
  (rel : free_group ℕ)
  (rel_index : ℕ)
  (inv : bool) :
  Π word₁ word₂ : free_group ℕ, M unit
| word₁       ⟨[], h⟩          := add_leaf old_word word₁ 1 rel rel_index inv
| word₁ word₂@⟨⟨i, n⟩ :: l, h⟩ :=
  add_leaf old_word word₁ word₂ rel rel_index inv >>
  add_leaves_of_rel_core
    (word₁ * of' i (of_add n.to_add.sign))
    (of' i (of_add (-n.to_add.sign)) * (word₂ : free_group ℕ))

meta def add_leaves_of_rel (word : free_group ℕ) (rel : free_group ℕ)
  (rel_index : ℕ) (inv : bool) : M unit :=
add_leaves_of_rel_core word rel rel_index inv 1 word

meta def grow_leaves : M unit :=
do l ← get_leaves,
  let path := l.min.iget,
  add_seen_erase_leaf path.fst path.snd,
  rels ← get_rels,
  rels.iterate
    (return ())
    (λ i rel m,
      m >>
      add_leaves_of_rel path.fst (rel⁻¹) i tt >>
      add_leaves_of_rel path.fst rel i ff
      )

meta def solve_aux : M unit :=
grow_leaves >> solve_aux

meta def solve (rels : list (free_group ℕ)) (word : free_group ℕ) : leaves × seen :=
run rels.to_buffer word solve_aux

-- #eval let rels := [of 0 * of 1 * (of 0)⁻¹ * (of 1)^ (-2 : int),
--   of 2 * of 1 * (of 2)⁻¹ * (of 3)⁻¹,
--   of 2 * of 0 * (of 2)⁻¹ * (of 0)⁻¹,
--   of 3 * of 1 * (of 3)⁻¹ * (of 1)⁻¹] in

--  (solve [of 0 * of 1 * (of 0)⁻¹ * (of 1)^ (-2 : int),
--   of 2 * of 1 * (of 2)⁻¹ * (of 3)⁻¹,
--   of 2 * of 0 * (of 2)⁻¹ * (of 0)⁻¹,
--   of 3 * of 1 * (of 3)⁻¹ * (of 1)⁻¹]
--   (of 0 * of 2 * of 1 * (of 2)⁻¹ * (of 0)⁻¹ * (of 3)^ (-2 : int))).2.to_list

end group_rel
