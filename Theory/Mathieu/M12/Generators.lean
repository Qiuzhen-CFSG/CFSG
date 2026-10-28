module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.List
public import Batteries
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Sporadic.Mathieu

/-- The first ATLAS standard generator in the degree-12 representation. -/
@[expose]
public def m12GeneratorA : Equiv.Perm (Fin 12) :=
  Equiv.swap (1 : Fin 12) 4 * Equiv.swap (3 : Fin 12) 10 *
    Equiv.swap (5 : Fin 12) 11 * Equiv.swap (6 : Fin 12) 12

/-- The second ATLAS standard generator in the degree-12 representation. -/
@[expose]
public def m12GeneratorB : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 8, 9] * List.formPerm [2, 3, 4] *
    List.formPerm [5, 12, 11] * List.formPerm [6, 10, 7]

/-- The first ATLAS standard generator has order two. -/
public theorem m12GeneratorA_order : orderOf m12GeneratorA = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The second ATLAS standard generator has order three. -/
public theorem m12GeneratorB_order : orderOf m12GeneratorB = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

end Sporadic.Mathieu
