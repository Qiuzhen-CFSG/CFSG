module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.GroupTheory.OrderOfElement

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Sporadic.Mathieu

/-- The first ATLAS standard generator in the degree-22 representation. -/
@[expose] public def m22GeneratorA : Equiv.Perm (Fin 22) :=
  Equiv.swap (1 : Fin 22) 13 * Equiv.swap (2 : Fin 22) 8 *
    Equiv.swap (3 : Fin 22) 16 * Equiv.swap (4 : Fin 22) 12 *
    Equiv.swap (6 : Fin 22) 22 * Equiv.swap (7 : Fin 22) 17 *
    Equiv.swap (9 : Fin 22) 10 * Equiv.swap (11 : Fin 22) 14

/-- The second ATLAS standard generator in the degree-22 representation. -/
@[expose] public def m22GeneratorB : Equiv.Perm (Fin 22) :=
  List.formPerm [1, 22, 3, 21] * List.formPerm [2, 18, 4, 13] *
    Equiv.swap (5 : Fin 22) 12 * List.formPerm [6, 11, 7, 15] *
    List.formPerm [8, 14, 20, 10] * Equiv.swap (17 : Fin 22) 19

/-- The first ATLAS standard generator has order two. -/
public theorem m22GeneratorA_order : orderOf m22GeneratorA = 2 := by
  apply orderOf_eq_prime
  · decide +kernel
  · decide +kernel

/-- The second ATLAS standard generator has order four. -/
public theorem m22GeneratorB_order : orderOf m22GeneratorB = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide +kernel : 0 < 4)
  · decide +kernel
  · intro p hp hp4
    have hpPow : p ∣ 2 ^ 2 := by simpa using hp4
    have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    have hpEq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
    subst p
    decide +kernel

end Sporadic.Mathieu
