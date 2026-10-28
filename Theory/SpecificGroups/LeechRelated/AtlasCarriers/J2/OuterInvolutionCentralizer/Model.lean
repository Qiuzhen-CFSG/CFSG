module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin

/-!
# The fourteen-point outer-centralizer model

These two permutations are the restrictions of explicit Hall--Janko words to
the fourteen fixed points of the outer involution. This module only defines
their generated subgroup. The comparison with the entire fixed subgroup and
the identification with PGL₂(7) are separate mathematical obligations.

Source: retained ATLAS `J2G1-p100B0` generators; GLS3, Table 5.3g, class 2C;
Aschbacher--Smith 16.1.5(8), printed p.1172. The restrictions are independently
checked in `Witnesses`; no group-computation output is assumed.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer

/-- Restriction of the first ATLAS generator to the ordered fixed points. -/
def modelA : Equiv.Perm (Fin 14) where
  toFun := ![1, 0, 4, 6, 2, 9, 3, 11, 12, 5, 13, 7, 8, 10]
  invFun := ![1, 0, 4, 6, 2, 9, 3, 11, 12, 5, 13, 7, 8, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Restriction of the displayed order-eight carrier word. -/
def modelB : Equiv.Perm (Fin 14) where
  toFun := ![2, 3, 5, 7, 8, 10, 11, 12, 4, 13, 0, 9, 6, 1]
  invFun := ![10, 13, 0, 1, 8, 2, 12, 3, 4, 11, 5, 6, 7, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- A concrete permutation group, with its generating pair retained. -/
def model : Subgroup (Equiv.Perm (Fin 14)) := Subgroup.closure {modelA, modelB}

theorem modelA_mem : modelA ∈ model := Subgroup.subset_closure (by simp)
theorem modelB_mem : modelB ∈ model := Subgroup.subset_closure (by simp)

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
