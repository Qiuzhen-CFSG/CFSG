module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Concrete candidates for the nonsplit Held centralizers

This module fixes three actual permutation groups on sixteen letters. Each is
specified by two explicit generators, with inverse tables checked by the Lean
kernel. The carriers are the generated subgroups, so subsequent alternatives
must construct multiplicative equivalences to these groups.

The first pair comes from the following elementary permutation construction
(using one-based labels here): take the four disjoint cycles
(1,2,3,4), (5,6,7,8), (9,10,11,12), (13,14,15,16), their squares, and the
products of their simultaneous rotation with a transposition and a four-cycle
of the four blocks. The second and third pairs are explicit degree-sixteen models
selected during finite-extension exploration. The tables below use zero-based
labels. The comparison with those constructions, completeness of the local
alternatives, and exclusion in a simple ambient group are separate proof
obligations; no extension or classification theorem is asserted here.

These coordinates support the splitting problem of Huppert--Blackburn,
*Finite Groups III*, XII.1.18(b), p.314, citing D. Held, J. Algebra 8 (1968),
436--449, DOI 10.1016/0021-8693(68)90054-9. They are independent computational
choices of generators, not permutations claimed to be printed in that source.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitModels

/-- An explicit generator of the first candidate. -/
@[expose] public def firstA : Equiv.Perm (Fin 16) where
  toFun := ![13, 14, 15, 12, 9, 10, 11, 8, 1, 2, 3, 0, 5, 6, 7, 4]
  invFun := ![11, 8, 9, 10, 15, 12, 13, 14, 7, 4, 5, 6, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit generator of the first candidate. -/
@[expose] public def firstB : Equiv.Perm (Fin 16) where
  toFun := ![10, 11, 8, 9, 2, 3, 0, 1, 6, 7, 4, 5, 12, 13, 14, 15]
  invFun := ![6, 7, 4, 5, 10, 11, 8, 9, 2, 3, 0, 1, 12, 13, 14, 15]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit generator of the second candidate. -/
@[expose] public def secondA : Equiv.Perm (Fin 16) where
  toFun := ![4, 1, 2, 11, 0, 14, 13, 7, 9, 8, 10, 3, 15, 6, 5, 12]
  invFun := ![4, 1, 2, 11, 0, 14, 13, 7, 9, 8, 10, 3, 15, 6, 5, 12]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit generator of the second candidate. -/
@[expose] public def secondB : Equiv.Perm (Fin 16) where
  toFun := ![6, 3, 7, 14, 12, 4, 10, 8, 5, 15, 1, 13, 2, 11, 0, 9]
  invFun := ![14, 10, 12, 1, 5, 8, 0, 2, 7, 15, 6, 13, 4, 11, 3, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit generator of the third candidate. -/
@[expose] public def thirdA : Equiv.Perm (Fin 16) where
  toFun := ![8, 9, 15, 14, 11, 10, 12, 13, 0, 1, 7, 6, 3, 2, 4, 5]
  invFun := ![8, 9, 13, 12, 14, 15, 11, 10, 0, 1, 5, 4, 6, 7, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- An explicit generator of the third candidate. -/
@[expose] public def thirdB : Equiv.Perm (Fin 16) where
  toFun := ![4, 5, 7, 6, 3, 2, 1, 0, 13, 12, 14, 15, 10, 11, 8, 9]
  invFun := ![7, 6, 5, 4, 0, 1, 3, 2, 14, 15, 12, 13, 9, 8, 10, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- The first concrete generated permutation subgroup. -/
@[expose] public def firstSubgroup : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure {firstA, firstB}

/-- The second concrete generated permutation subgroup. -/
@[expose] public def secondSubgroup : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure {secondA, secondB}

/-- The third concrete generated permutation subgroup. -/
@[expose] public def thirdSubgroup : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure {thirdA, thirdB}

/-- The first candidate carrier, with its inherited permutation-group law. -/
public abbrev First := firstSubgroup

/-- The second candidate carrier, with its inherited permutation-group law. -/
public abbrev Second := secondSubgroup

/-- The third candidate carrier, with its inherited permutation-group law. -/
public abbrev Third := thirdSubgroup

end Theory.GroupTheory.HeldM22A10.NonsplitModels
