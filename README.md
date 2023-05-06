# Single relator groups

This repository contains an implementation of Magnus' method for solving the word problem in one relator groups. There is also a Lean tactic `group1r` which will prove equalities of group terms, with one equality as a hypothesis. There is also a tactic for proving equalities in groups presented by finitely many relations, this tactic is non-terminating if the equality is not provable.

## Navigating the repository

* The definition `solve` in the file `solve.lean` is the algorithm for solving the word problem in one relator groups.
* The tactic `group1r` for proving equalities of group expressions is in the file `tactic/group1r.lean`
* Examples of tests of the `group_rel` tactic for more than one rerlation can be found in `multirelation/approach2/test.lean`, and the tactic itself is contained in `multirelation/approach2/tactic.lean`
