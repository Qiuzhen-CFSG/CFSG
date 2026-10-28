module
public import Theory.Mathieu.M22.Basic
public import Mathlib.Tactic.FinCases

/-!
# An element of order eight in the degree-22 Mathieu group

The word `(ab)^3 b a b^3` in the native ATLAS generators has order eight.
We check its explicit permutation table before taking powers, keeping the
kernel calculation small. This supplies the exponent obstruction to an M₂₂
section in binary rank-one groups.

Source: the ATLAS degree-22 generators in `M22.Generators`; used in the
model comparison of Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu
private def eightPerm : Equiv.Perm (Fin 22) :=
  (m22GeneratorA * m22GeneratorB)^3 * m22GeneratorB * m22GeneratorA * m22GeneratorB^3
private theorem eightPerm_mem : eightPerm ∈ M22 := by
  exact M22.mul_mem (M22.mul_mem (M22.mul_mem
    (M22.pow_mem (M22.mul_mem m22GeneratorA_mem_M22 m22GeneratorB_mem_M22) 3)
    m22GeneratorB_mem_M22) m22GeneratorA_mem_M22) (M22.pow_mem m22GeneratorB_mem_M22 3)
private def eightTable : Equiv.Perm (Fin 22) where
  toFun i := ![5,20,21,7,14,17,9,2,18,19,12,8,1,6,4,0,11,15,10,3,16,13] i
  invFun i := ![15,12,7,19,14,0,13,3,11,6,18,16,10,21,4,17,20,5,8,9,1,2] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel
private theorem eightPerm_table : eightPerm = eightTable := by
  ext i
  fin_cases i <;> decide +kernel
private theorem eightPerm_pow_eight : eightPerm ^ 8 = 1 := by
  rw [eightPerm_table]
  decide +kernel
private theorem eightPerm_pow_four : eightPerm ^ 4 ≠ 1 := by
  rw [eightPerm_table]
  decide +kernel
/-- An order-eight element of the literal degree-22 Mathieu group. -/
theorem m22_exists_order_eight : ∃ x : M22, orderOf x = 8 := by
  refine ⟨⟨eightPerm,eightPerm_mem⟩,?_⟩
  rw [←orderOf_coe]
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide : 0 < 8) eightPerm_pow_eight
  intro p hp hp8
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2^3 from hp8)
  have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
  subst p
  exact eightPerm_pow_four
end Sporadic.Mathieu
