module

public import Theory.SpecificGroups.LieType.TheoremDRootNormalizer.ThreeTorus
import Mathlib.Tactic

/-!
# Higher-rank split exceptional groups are not quasithin

For E6, E7 and E8, the simple coroots numbered 0, 3 and 5 are pairwise
orthogonal. Their three squared root characters separate all field-unit
parameters in characteristic two, including after the literal central
quotient. Thus no assumption on the order of the E6 center is necessary.
For F4, the first three simple nodes have Cartan determinant two. Their
three character equations again force every parameter to be one.

The imported construction places these tori in genuine root normalizers and
restricts them to elementary odd-prime subgroups of rank three. All four
conclusions need only quasithinness and a finite binary field of order > 2.
Source: Aschbacher–Smith A.2.18, printed p.40, used for Theorem D/14.8.2(1),
printed pp.1078–1079. No parabolic, induction or simplicity input is used.
-/

public section

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
noncomputable section
namespace ExceptionalSplit.TheoremDRootNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
local instance : Fintype typeE6Roots := Fintype.ofFinite _
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

theorem not_quasithin_e6 (hq : 2 < Nat.card F) : ¬ IsQuasithin (E6 F) := by
  let j : Fin 3 → typeE6RootPairing_base.support :=
    fun i => typeE6RootPairing_baseEquiv (![0, 3, 5] i)
  apply not_quasithin_of_three hq j
  apply orthogonal_three_separate j
  intro i k
  change typeE6RootPairing_base.cartanMatrix _ _ = _
  rw [typeE6RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases k <;> norm_num [typeE6CartanMatrix, Fin.ext_iff]

theorem not_quasithin_e7 (hq : 2 < Nat.card F) : ¬ IsQuasithin (E7 F) := by
  let j : Fin 3 → typeE7RootPairing_base.support :=
    fun i => typeE7RootPairing_baseEquiv (![0, 3, 5] i)
  apply not_quasithin_of_three hq j
  apply orthogonal_three_separate j
  intro i k
  change typeE7RootPairing_base.cartanMatrix _ _ = _
  rw [typeE7RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases k <;> norm_num [typeE7CartanMatrix, Fin.ext_iff]

theorem not_quasithin_e8 (hq : 2 < Nat.card F) : ¬ IsQuasithin (E8 F) := by
  let j : Fin 3 → typeE8RootPairing_base.support :=
    fun i => typeE8RootPairing_baseEquiv (![0, 3, 5] i)
  apply not_quasithin_of_three hq j
  apply orthogonal_three_separate j
  intro i k
  change typeE8RootPairing_base.cartanMatrix _ _ = _
  rw [typeE8RootPairing_base_cartan_apply]
  fin_cases i <;> fin_cases k <;> norm_num [typeE8CartanMatrix, Fin.ext_iff]

theorem not_quasithin_f4 (hq : 2 < Nat.card F) : ¬ IsQuasithin (F4 F) := by
  let j : Fin 3 → typeF4RootPairing_base.support :=
    fun i => typeF4RootPairing_baseEquiv i.castSucc
  apply not_quasithin_of_three hq j
  intro a ha
  have hp (i k : Fin 3) : typeF4RootPairing.pairingIn ℤ (j i) (j k) =
      typeF4CartanMatrix i.castSucc k.castSucc :=
    typeF4RootPairing_base_cartan_apply _ _
  have h0 : a 0 ^ 2 = a 1 := by
    apply mul_inv_eq_one.mp
    simpa [hp, typeF4CartanMatrix] using ha 0
  have h1 : (a 0)⁻¹ * a 1 ^ 2 * (a 2 ^ 2)⁻¹ = 1 := by
    simpa [hp, typeF4CartanMatrix] using ha 1
  have h2 : a 1 = a 2 ^ 2 := by
    apply inv_mul_eq_one.mp
    simpa [hp, typeF4CartanMatrix] using ha 2
  rw [← h2, pow_two, mul_assoc, mul_inv_cancel_right] at h1
  have hab : a 0 = a 1 := inv_mul_eq_one.mp h1
  have ha0 : a 0 = 1 := by
    apply mul_left_cancel (a := a 0)
    simpa only [pow_two, mul_one] using h0.trans hab.symm
  have ha1 : a 1 = 1 := hab.symm.trans ha0
  have ha2 : a 2 = 1 := unit_square_eq_one (h2.symm.trans ha1)
  funext i
  fin_cases i
  · exact ha0
  · exact ha1
  · exact ha2

end ExceptionalSplit.TheoremDRootNormalizer
