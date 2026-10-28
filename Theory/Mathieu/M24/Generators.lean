module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Perm.List

namespace Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The first ATLAS standard generator in the degree-24 representation. -/
@[expose]
public def m24GeneratorA : Equiv.Perm (Fin 24) :=
  Equiv.swap (1 : Fin 24) 4 * Equiv.swap (2 : Fin 24) 7 *
    Equiv.swap (3 : Fin 24) 17 * Equiv.swap (5 : Fin 24) 13 *
    Equiv.swap (6 : Fin 24) 9 * Equiv.swap (8 : Fin 24) 15 *
    Equiv.swap (10 : Fin 24) 19 * Equiv.swap (11 : Fin 24) 18 *
    Equiv.swap (12 : Fin 24) 21 * Equiv.swap (14 : Fin 24) 16 *
    Equiv.swap (20 : Fin 24) 24 * Equiv.swap (22 : Fin 24) 23

/-- The second ATLAS standard generator in the degree-24 representation. -/
@[expose]
public def m24GeneratorB : Equiv.Perm (Fin 24) :=
  List.formPerm [1, 4, 6] * List.formPerm [2, 21, 14] *
    List.formPerm [3, 9, 15] * List.formPerm [5, 18, 10] *
    List.formPerm [13, 17, 16] * List.formPerm [19, 24, 23]

/-- The first ATLAS standard generator has order two. -/
public theorem m24GeneratorA_order : orderOf m24GeneratorA = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The second ATLAS standard generator has order three. -/
public theorem m24GeneratorB_order : orderOf m24GeneratorB = 3 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

end Sporadic.Mathieu
