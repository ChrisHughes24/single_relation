import P
/-!
# Solve by trivial
This file contains one definition, `solve_by_trivial`.

`solve_by_trivial` solves the word problem in the easy case when
every letter in `w` is already in `T`.
-/

open semidirect_product

def solve_by_trivial  {ι : Type} [decidable_eq ι] (T : set ι)
  [decidable_pred T] (w : free_group ι) (vars_w : list ι) :
  option (P (free_group ι)) :=
guard (vars_w.all (∈ T)) >> return (inr w)
