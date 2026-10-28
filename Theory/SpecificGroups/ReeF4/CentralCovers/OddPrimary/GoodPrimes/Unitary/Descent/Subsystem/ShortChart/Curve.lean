module
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Support
import all Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart.Coefficients
import all Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleComparison
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.SourceModel.Transport

/-!
# Sparse formulas for the actual short-root curves

The integral Geck divided powers, reduced modulo two and transported to any
field of characteristic two, equal the checked binary coefficient tables.
The third divided powers vanish. Summing their sparse row supports gives the
literal root-curve action used by the short-A₂ chart.

The internal imports deliberately reuse the integral coefficient computation
from `DerivedTits.Realization.SimpleComparison`; no new root action is assumed.
-/

namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
open scoped Matrix
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup.StandardRootSystem
open TwistedE6.FoldedSubsystem.F4Identification
open ReeF4.DerivedTits.Realization.SimpleComparison
namespace Coefficients
noncomputable section
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _

private theorem actual_positive (k : Bool) (n : Fin 3) (r c : Index) :
    (eDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) (n.val + 1)
      (basisCoordinates r) (basisCoordinates c) : ZMod 2) = coefficient k n r c := by
  change (eDividedPower (node (if k then 2 else 3)) (n.val + 1) (coord r) (coord c) : ZMod 2) = _
  fin_cases n
  · rw [eDividedPower_one, eLinear_entry]
    exact positive_table k 0 r c
  · rw [eHigher_entry _ 0]
    exact positive_table k 1 r c
  · rw [eHigher_entry _ 1]
    exact positive_table k 2 r c

private theorem actual_negative (k : Bool) (n : Fin 3) (r c : Index) :
    (fDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) (n.val + 1)
      (basisCoordinates r) (basisCoordinates c) : ZMod 2) =
      coefficient k n (reverseIndex r) (reverseIndex c) := by
  change (fDividedPower (node (if k then 2 else 3)) (n.val + 1) (coord r) (coord c) : ZMod 2) = _
  rw [fDividedPower, mul_omega_entry, omega_mul_entry,
    ← coord_reverse, ← coord_reverse]
  exact actual_positive k n (reverseIndex r) (reverseIndex c)

private theorem cubic_zero : ∀ (k : Bool) (r c : Index), coefficient k 2 r c = 0 := by
  let dec : Decidable (∀ (k : Bool) (r c : Index), coefficient k 2 r c = 0) :=
    @Fintype.decidableForallFintype Bool _ (fun k =>
      @Fintype.decidableForallFintype Index _ (fun r =>
        @Fintype.decidableForallFintype Index _
          (fun c => ZMod.decidableEq 2 _ _) inferInstance) inferInstance) inferInstance
  exact @of_decide_eq_true _ dec (by decide +kernel)

variable (F : Type*) [Field F] [CharP F 2]
private theorem scalar_positive (k : Bool) (n : Fin 3) (r c : Index) :
    (eDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) (n.val + 1)
      (basisCoordinates r) (basisCoordinates c) : F) =
      ZMod.castHom (dvd_refl 2) F (coefficient k n r c) := by
  have h := congrArg (ZMod.castHom (dvd_refl 2) F) (actual_positive k n r c)
  simpa only [map_intCast] using h

private theorem scalar_negative (k : Bool) (n : Fin 3) (r c : Index) :
    (fDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) (n.val + 1)
      (basisCoordinates r) (basisCoordinates c) : F) =
      ZMod.castHom (dvd_refl 2) F (coefficient k n (reverseIndex r) (reverseIndex c)) := by
  have h := congrArg (ZMod.castHom (dvd_refl 2) F) (actual_negative k n r c)
  simpa only [map_intCast] using h

private def scalar (s k : Bool) (n : Fin 3) : Matrix Index Index F := fun r c =>
  ZMod.castHom (dvd_refl 2) F
    (if s then coefficient k n r c else coefficient k n (reverseIndex r) (reverseIndex c))

private def curveMatrix (s k : Bool) (t : F) : Matrix Index Index F :=
  1 + t • scalar F s k 0 + t ^ 2 • scalar F s k 1

set_option backward.isDefEq.respectTransparency false in
private theorem coverSimple_entry (s k : Bool) (t : F) (r c : Index) :
    (coverSimple F s (if k then 2 else 3) t).val.val
      (basisCoordinates r) (basisCoordinates c) = curveMatrix F s k t r c := by
  classical
  rw [coverSimple_val]
  cases s
  · change negativeMatrix _ t _ _ = _
    rw [negativeMatrix_formula]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
      smul_eq_mul, Matrix.one_apply, sourceIndex]
    have h0 : (fDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 1
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 0 (reverseIndex r) (reverseIndex c)) :=
      scalar_negative F k 0 r c
    have h1 : (fDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 2
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 1 (reverseIndex r) (reverseIndex c)) :=
      scalar_negative F k 1 r c
    have h2 : (fDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 3
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 2 (reverseIndex r) (reverseIndex c)) :=
      scalar_negative F k 2 r c
    calc
      _ = (if basisCoordinates r = basisCoordinates c then 1 else 0) +
          t * ZMod.castHom (dvd_refl 2) F (coefficient k 0 (reverseIndex r) (reverseIndex c)) +
          t ^ 2 * ZMod.castHom (dvd_refl 2) F (coefficient k 1 (reverseIndex r) (reverseIndex c)) +
          t ^ 3 * ZMod.castHom (dvd_refl 2) F (coefficient k 2 (reverseIndex r) (reverseIndex c)) := by
        exact congrArg₂ (· + ·)
          (congrArg₂ (· + ·) (congrArg (fun x => _ + t * x) h0)
            (congrArg (fun x => t ^ 2 * x) h1))
          (congrArg (fun x => t ^ 3 * x) h2)
      _ = _ := by
        rw [cubic_zero]
        simp [curveMatrix, scalar, Matrix.one_apply, basisCoordinates.injective.eq_iff]
  · change positiveMatrix _ t _ _ = _
    rw [positiveMatrix_formula]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Int.coe_castRingHom,
      smul_eq_mul, Matrix.one_apply, sourceIndex]
    have h0 : (eDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 1
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 0 r c) :=
      scalar_positive F k 0 r c
    have h1 : (eDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 2
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 1 r c) :=
      scalar_positive F k 1 r c
    have h2 : (eDividedPower (typeF4RootPairing_baseEquiv (if k then 2 else 3)) 3
        (basisCoordinates r) (basisCoordinates c) : F) =
          ZMod.castHom (dvd_refl 2) F (coefficient k 2 r c) :=
      scalar_positive F k 2 r c
    calc
      _ = (if basisCoordinates r = basisCoordinates c then 1 else 0) +
          t * ZMod.castHom (dvd_refl 2) F (coefficient k 0 r c) +
          t ^ 2 * ZMod.castHom (dvd_refl 2) F (coefficient k 1 r c) +
          t ^ 3 * ZMod.castHom (dvd_refl 2) F (coefficient k 2 r c) := by
        exact congrArg₂ (· + ·)
          (congrArg₂ (· + ·) (congrArg (fun x => _ + t * x) h0)
            (congrArg (fun x => t ^ 2 * x) h1))
          (congrArg (fun x => t ^ 3 * x) h2)
      _ = _ := by
        rw [cubic_zero]
        simp [curveMatrix, scalar, Matrix.one_apply, basisCoordinates.injective.eq_iff]

private theorem scalar_support (s k : Bool) (n : Fin 3) (r c : Index) :
    scalar F s k n r c = if c ∈ rowSupport s k n r then 1 else 0 := by
  change ZMod.castHom (dvd_refl 2) F
    (if s then coefficient k n r c else
      coefficient k n (reverseCoordinates r) (reverseCoordinates c)) = _
  rw [coefficient_support]
  split_ifs <;> simp

private theorem scalar_sum (s k : Bool) (n : Fin 3) (r : Index) (w : Index → F) :
    ∑ c, scalar F s k n r c * w c = ∑ c ∈ rowSupport s k n r, w c := by
  simp only [scalar_support, ite_mul, one_mul, zero_mul]
  simp

public theorem coverSimple_mulVec (s k : Bool) (t : F) (w : Index → F) (r : Index) :
    ((coverSimple F s (if k then 2 else 3) t).val.val *ᵥ
      (w ∘ basisCoordinates.symm)) (basisCoordinates r) =
        w r + t * ∑ c ∈ rowSupport s k 0 r, w c +
          t ^ 2 * ∑ c ∈ rowSupport s k 1 r, w c := by
  classical
  change (∑ c, (coverSimple F s (if k then 2 else 3) t).val.val
    (basisCoordinates r) c * (w ∘ basisCoordinates.symm) c) = _
  rw [← basisCoordinates.sum_comp]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, coverSimple_entry,
    curveMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, add_mul, Finset.sum_add_distrib, mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, scalar_sum, scalar_sum]
  simp

end
end Coefficients
end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.ShortChart
