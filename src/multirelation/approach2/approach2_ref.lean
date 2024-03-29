import .free_group2
import data.buffer
import tactic.delta_instance
import data.list.min_max
import tactic.norm_num
-- This is the main file
namespace group_rel
open native free_group

-- use an rb_lmap

instance {α : Type} : inhabited (buffer α) := ⟨mk_buffer⟩

@[derive inhabited] structure relation : Type :=
(rel : free_group)
(letters : buffer (ℕ × bool)) -- the actual word
(indices : buffer (list ℕ))   -- given a letter, a
  -- buffer containing a list of the locations of that letter not inverted
(inv_indices : buffer (list ℕ)) -- given a letter, a
  -- buffer containing a list of the locations of that letter inverted
(length : ℕ) --length of the relation
(rel_index : ℕ) -- index of my relation in my starting list
(is_inv : bool) -- is it an inverse of a relation in my starting list?

structure rewrite : Type :=
(word_letter_index : ℕ)
(rel_letter_index : ℕ)
(cancel_length : ℕ)

@[derive inhabited] structure path_step : Type :=
(rel_index : ℕ) -- Index of the relator used to make the rewrite
(rel_is_inv : bool) -- Boolean representing whether the relator or
  --its inverse was used to make the substitution
(old_word : free_group) -- word before the substitution was made
(new_word : free_group) -- word after the substitution was made
(new_word_cost : ℕ) -- cost of the new word
(word_letter_index : ℕ) -- Letter index in the old word,
  -- indicating where the substitution was made
(rel_letter_index : ℕ) -- Letter index in the relator indicating
  -- which letter in the relator was substituted.

meta structure rewrites : Type :=
(starting_rewrites : rb_map ℕ ℕ) -- (rel_starting_index, cancel_length)
(completed_starting_rewrites : rb_map ℕ ℕ)
(current_rewrites : list rewrite)

@[derive monad] meta def tree_m : Type → Type :=
except_t path_step
  (reader_t (
      tactic.ref (rb_lmap ℕ path_step) × --leaves, indexed by cost
      tactic.ref (rb_map free_group path_step) ×--seen
      buffer relation × ℕ)
    tactic)

meta instance {α : Type} : has_coe (option α) (tree_m α) :=
⟨λ o, o.elim ⟨return (except.error ⟨1, ff, 1, 1, 1, 1, 1⟩)⟩ return⟩

meta def get_rels : tree_m (buffer relation) :=
do x ← except_t.lift $ reader_t.read, return x.2.2.1

meta def get_no_atoms : tree_m ℕ :=
do x ← except_t.lift $ reader_t.read, return x.2.2.2

meta def get_leaves : tree_m (rb_lmap ℕ path_step) :=
do x ← except_t.lift $ reader_t.read,
except_t.lift $ reader_t.lift $ tactic.read_ref x.1

meta def get_seen : tree_m (rb_map free_group path_step) :=
do x ← except_t.lift $ reader_t.read,
except_t.lift $ reader_t.lift $ tactic.read_ref x.2.1

meta def write_leaves (rb : rb_lmap ℕ path_step) : tree_m unit :=
do x ← except_t.lift $ reader_t.read,
except_t.lift $ reader_t.lift $ tactic.write_ref x.1 rb

meta def write_seen (rb : rb_map free_group path_step) : tree_m unit :=
do x ← except_t.lift $ reader_t.read,
except_t.lift $ reader_t.lift $ tactic.write_ref x.2.1 rb

meta def trace_tree_size : tree_m unit :=
do l ← get_leaves, s ← get_seen,
let n := (l.to_list.map prod.snd).join.length,
let m := l.to_list.length,
trace ("tree size = " ++ repr n ++ "\n" ++ "seen nodes = " ++ repr m) return ()

meta def get_min_leaf_and_erase : tree_m path_step :=
do leaves ← get_leaves,
seen ← get_seen,
l ← leaves.min,
match l with
| [] := return (default _)
| [p]               :=
  match seen.contains p.new_word with
  | ff := do
    write_leaves (leaves.erase p.new_word_cost),
    write_seen (seen.insert p.new_word p),
    return p
  | tt := do
    write_leaves (leaves.erase p.new_word_cost),
    get_min_leaf_and_erase
  end
| (p :: l'@(_ :: _)) :=
  match seen.contains p.new_word with
  | ff := do
    write_leaves (rb_map.insert leaves p.new_word_cost l'),
    write_seen (seen.insert p.new_word p),
    return p
  | tt := do
    write_leaves (rb_map.insert leaves p.new_word_cost l'),
    get_min_leaf_and_erase
  end
end

meta def stop (p : path_step) : tree_m path_step :=
⟨return (except.error p)⟩

meta structure leaf_data :=
(rel : relation)
(word : free_group)

@[derive monad] meta def leaves_m (α : Type) : Type :=
reader_t leaf_data (state_t rewrites tree_m) α

meta instance {α : Type} : has_coe (option α) (leaves_m α) :=
⟨λ o, reader_t.lift $ state_t.lift o⟩

meta def tree_m.lift {α : Type} (m : tree_m α) : leaves_m α :=
reader_t.lift $ state_t.lift m

meta def leaves_m.trace (s: string) : leaves_m unit :=
trace s return ()

meta def get_rewrites : leaves_m rewrites := reader_t.lift state_t.get

meta def get_leaf_data : leaves_m leaf_data := reader_t.read

meta def add_path (rw : rewrite) : leaves_m unit :=
do ⟨rel, old_word⟩ ← get_leaf_data,
  let new_word := cyclically_reduce (old_word.take rw.word_letter_index
    * (rel.rel.rotate rw.rel_letter_index)⁻¹
    * old_word.drop rw.word_letter_index), --check if this is correct
  no_atoms : ℕ ← tree_m.lift get_no_atoms,
  let new_cost := cost no_atoms new_word,
  let new_path : path_step :=
    ⟨rel.rel_index, rel.is_inv, old_word, new_word,
      new_cost, rw.word_letter_index, rw.rel_letter_index⟩,
  leaves ← tree_m.lift get_leaves,
  tree_m.lift $ write_leaves (leaves.insert new_cost new_path)

meta def match_starting_rewrites : leaves_m unit :=
do c ← get_rewrites,
⟨rel, word⟩ ← get_leaf_data,
  c.starting_rewrites.fold
    (return ())
    (λ rel_letter_index cancel_length m,
      add_path ⟨0, rel_letter_index, cancel_length⟩ >> m),
  c.current_rewrites.mfoldl
    (λ _ rw,
      do c ← get_rewrites,
        match c.completed_starting_rewrites.find
          ((rw.rel_letter_index + rw.cancel_length) % rel.length) with
        | (some length) :=
            add_path ⟨rw.word_letter_index, rw.rel_letter_index, rw.cancel_length + length⟩
        | none          := add_path rw
        end)
    ()

-- Not the proper thing but it works
meta def match_starting_rewrites' : leaves_m unit :=
do c ← get_rewrites,
ld ← get_leaf_data,
c.current_rewrites.mfoldl (λ _, add_path) (),
c.starting_rewrites.fold (return ())
  (λ a b m, m >> add_path ⟨0, a, b⟩),
c.completed_starting_rewrites.fold (return ())
  (λ a b m, m >> add_path ⟨0, a, b⟩)

meta def get_indices (l : ℕ × bool) : leaves_m (list ℕ) :=
do ld ← get_leaf_data,
return (cond l.2 (ld.rel.inv_indices.read' l.1) (ld.rel.indices.read' l.1))

meta def add_starting_rewrite (index : ℕ) : leaves_m unit :=
reader_t.lift $ state_t.modify (λ x, ⟨x.1.insert index 1, x.2, x.3⟩)

def sub_one_mod (a b : ℕ) : ℕ :=
nat.cases_on a (b - 1) id

meta def grow_leaves_aux' :
  Π (word₁ word₂ : free_group) (word₂_length : ℕ), leaves_m unit
| []      l₂ _ := return ()
| (x::l₁) l₂ word₂_length  :=
do l ← get_indices x,
  l.mfoldl
    (λ _ index, add_path ⟨word₂_length, index, 1⟩)
    (),
  grow_leaves_aux' l₁ (x::l₂) word₂_length.succ


-- Maybe don't bother trying to be too efficient about it
meta def grow_leaves_aux :
  Π (word₁ word₂ : free_group) (word₂_length : ℕ), leaves_m unit
| []      l₂ _ := match_starting_rewrites'
| (x::l₁) [] _ :=
  do l ← get_indices x,
  l.mfoldl
    (λ _ index, add_starting_rewrite index)
    (),
  rws ← get_rewrites,
  grow_leaves_aux l₁ [x] 1
| word₁@(x::l₁) word₂@(y::l₂) word₂_length :=
  do ld ← get_leaf_data,
  rw ← get_rewrites,
  (cr : list rewrite) ← rw.current_rewrites.mfoldl
    (λ cr rw,
      if ld.rel.letters.read' ((rw.rel_letter_index + rw.cancel_length) % ld.rel.length)
          = x
        then return (rewrite.mk rw.1 rw.2 rw.3.succ :: cr)
        else add_path rw >> return cr)
     [],
  let ((sr : rb_map ℕ ℕ), (csr : rb_map ℕ ℕ)) :=
    rw.starting_rewrites.fold (rw.starting_rewrites, rw.completed_starting_rewrites)
      (λ rel_letter_index cancel_length ⟨sr, csr⟩,
        if ld.rel.letters.read' ((rel_letter_index + cancel_length) % ld.rel.length)
            = x
          then (sr.insert rel_letter_index cancel_length.succ, csr)
          else (sr.erase rel_letter_index,
            csr.insert rel_letter_index cancel_length.succ)),
  reader_t.lift (state_t.modify (λ rw, ⟨sr, csr, cr⟩)),
  l ← get_indices x,
  l.mfoldl
    (λ _ index,
      if ld.rel.letters.read' (sub_one_mod index ld.rel.length) = y
        then return ()
        else
          reader_t.lift $ state_t.modify
            (λ rw, ⟨rw.1, rw.2, ⟨word₂_length, index, 1⟩::rw.3⟩))
    (),
  grow_leaves_aux l₁ (x::word₂) word₂_length.succ

meta def grow_leaves (rel : relation) (word : free_group) : tree_m unit :=
state_t.run
  (reader_t.run
    (grow_leaves_aux word 1 0) ⟨rel, word⟩)
  ⟨mk_rb_map, mk_rb_map, []⟩ >>
return ()

meta def solve_aux : tree_m path_step :=
do p ← get_min_leaf_and_erase,
  if p.new_word = 1
  then trace_tree_size >> stop p
  else do rels ← get_rels,
    rels.iterate
      (return ())
      (λ _ rel m, grow_leaves rel p.new_word >> m) >>
    solve_aux

meta def make_relation (r : free_group) (rel_index : ℕ) (is_inv : bool)
  (max_letter : ℕ) : relation :=
let empty_buffer : buffer (list ℕ) := list.to_buffer (list.repeat [] (max_letter + 1)) in
{ rel := r,
  letters := list.to_buffer r,
  indices := r.foldl_with_index (λ index b i, cond i.2 b
    (b.write' i.1 (index :: b.read' i.1)))
    empty_buffer,
  inv_indices := r.foldl_with_index (λ index b i, cond (bnot i.2) b
    (b.write' i.1 (index :: b.read' i.1)))
    empty_buffer,
  length := r.length,
  rel_index := rel_index,
  is_inv := is_inv }

meta def make_rels (rels : list (free_group)) (max_letter : ℕ) : buffer relation :=
rels.foldl_with_index
  (λ i b rel, (b.push_back (make_relation rel i ff max_letter)).push_back
    (make_relation (rel⁻¹) i tt max_letter))
  mk_buffer

def max_letter (w : free_group) : ℕ :=
(w.argmax (λ b : ℕ × bool, b.1)).iget.fst

meta def solve (rels : list (free_group)) (word : free_group) (no_atoms : ℕ) :
  tactic (path_step × rb_map (free_group) path_step) :=
let max_letter : ℕ := max (max_letter (rels.argmax max_letter).iget) (max_letter word) in
let i1 := except_t.run solve_aux in
let word_cost := cost max_letter word in
do tactic.using_new_ref (rb_lmap.insert (rb_lmap.mk _ path_step) word_cost
    ⟨0, ff, 1, word, word_cost, 0, 0⟩) $ λ leaves,
do tactic.using_new_ref mk_rb_map $ λ seen,
do i2 ← reader_t.run i1
  (leaves, seen, make_rels rels max_letter, no_atoms),
--seen ← tactic.read_ref i2.2.1,
except.cases_on i2 (λ x, do seen ← tactic.read_ref seen, return (x, seen))
  (λ x, failure)

-- meta def solve' (rels : list (free_group)) (word : free_group) (no_atoms) :
--   option (path_step × rb_lmap (ℕ × ℕ) (path_step)) :=
-- let max_letter : ℕ := max (max_letter (rels.argmax max_letter).iget) (max_letter word) in
-- let i1 := except_t.run solve_aux in
-- let i2 := state_t.run i1
--   (rb_lmap.insert mk_rb_map (word.length, 0)
--     ⟨0, ff, 1, word, word.length, 0, 0, 0⟩,
--     mk_rb_map) in
-- let i3 := reader_t.run i2 (make_rels rels max_letter, no_atoms) in
-- except.cases_on i3.1 (λ _, none) (λ x, return (x, i3.2.1))

meta def trace_path_core : Π (word : free_group)
  (seen : rb_map free_group path_step), list path_step
| word seen :=
let p := (seen.find word).iget in
  if p.old_word = 1
    then []
    else p :: trace_path_core p.old_word seen

meta def trace_path (seen : rb_map free_group path_step) : list path_step :=
trace_path_core 1 seen

universe u

meta def check_path_step (rels : list (free_group)) : path_step → bool
| ⟨rel_index, rel_is_inv, old_word, new_word, _, word_letter_index, rel_letter_index⟩ :=
let rel : free_group :=
  cyclically_reduce (cond rel_is_inv ((rels.nth rel_index).iget⁻¹) (rels.nth rel_index).iget) in
new_word = cyclically_reduce (old_word.take word_letter_index * (rel.rotate rel_letter_index)⁻¹ *
  old_word.drop word_letter_index)

meta def check_path (rels : list (free_group)): list path_step → option path_step
| [] := none
| [p] := none
| (p₁::p₂::l) :=
if p₁.old_word = p₂.new_word ∧
check_path_step rels p₁ then check_path (p₂ :: l)
else p₁

instance : has_repr (path_step) :=
⟨λ p, repr p.new_word⟩

end group_rel
