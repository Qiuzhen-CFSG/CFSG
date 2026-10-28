module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.IntegralModel
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.Opposition
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.RoutedCurves

/-!
# From signed integral commutators to the actual F4 root curves

For either simple direction, the integral Geck divided powers satisfy
`E² = 2B` and `BE = 0`; the cubic divided power vanishes for F4. The integral
coefficient argument therefore turns infinitesimal intertwining into
adjoint equivariance over every field, including characteristic three.
The generic Tits-word transport then covers all the literal root curves.

The positive integral commutators and signed opposition covariance are proved
in the imported modules. They discharge both infinitesimal premises in the
final theorem `rootCurve_equivariant`, for the fixed signed map and the literal
canonical root curves. Neither finiteness nor a restriction on characteristic
is needed for equivariance. This supplies exactly the equivariance premise of
`CoverCenter.center_eq_bot_of_adjointMap`; injectivity remains a separate input
to that center theorem. The parent assembly is not imported here.

Sources: the integral Geck divided-power construction and GLS3 §§2.2–2.6.
-/

public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

/-- Positive-simple equivariance, with only the integral operator commutator
left to be established for the fixed signed map. -/
theorem positive_simple_equivariant_of_integral_commutators
    (F : Type*) [Field F] (hE : PositiveIntegralCommutators)
    (i : typeF4RootPairing_base.support) (t : F) :
    Equivariant (adjointMap F) (positiveUnit i t) := by
  have hEE : eMatrix (P := typeF4RootPairing) i * eMatrix i =
      (2 : ℤ) • eDividedPower i 2 := by
    simpa [Nat.cast_smul_eq_nsmul] using
      eDividedPower_mul (P := typeF4RootPairing) i 1 1
  have hBE : eDividedPower (P := typeF4RootPairing) i 2 * eMatrix i = 0 := by
    simpa [ReeF4.WordRelations.eDividedPower_three] using
      eDividedPower_mul (P := typeF4RootPairing) i 2 1
  have hg : (positiveUnit i t : Matrix Coordinate Coordinate F) =
      1 + t • (eMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) +
        t ^ 2 • (eDividedPower (P := typeF4RootPairing) i 2).map (Int.castRingHom F) := by
    simp only [positiveUnit_val, positiveMatrix_formula, eDividedPower_one,
      ReeF4.WordRelations.eDividedPower_three, Matrix.map_zero _ (map_zero _),
      smul_zero, add_zero]
  simpa only [integralCoordinateOperator_map, adjointMap] using
    EquivarianceIntegration.equivariant_of_integral_commutator integralCoordinateOperator
      (eMatrix (P := typeF4RootPairing) i) (eDividedPower i 2) hEE hBE (hE i)
      t (positiveUnit i t) hg

/-- The negative direction uses its actual integral lowering operator. -/
theorem negative_simple_equivariant_of_integral_commutators
    (F : Type*) [Field F] (hF : NegativeIntegralCommutators)
    (i : typeF4RootPairing_base.support) (t : F) :
    Equivariant (adjointMap F) (negativeUnit i t) := by
  have hFF : fMatrix (P := typeF4RootPairing) i * fMatrix i =
      (2 : ℤ) • fDividedPower i 2 := by
    simpa [Nat.cast_smul_eq_nsmul] using
      fDividedPower_mul (P := typeF4RootPairing) i 1 1
  have hBF : fDividedPower (P := typeF4RootPairing) i 2 * fMatrix i = 0 := by
    simpa [ReeF4.WordRelations.fDividedPower_three] using
      fDividedPower_mul (P := typeF4RootPairing) i 2 1
  have hg : (negativeUnit i t : Matrix Coordinate Coordinate F) =
      1 + t • (fMatrix (P := typeF4RootPairing) i).map (Int.castRingHom F) +
        t ^ 2 • (fDividedPower (P := typeF4RootPairing) i 2).map (Int.castRingHom F) := by
    simp only [negativeUnit_val, negativeMatrix_formula, fDividedPower_one,
      ReeF4.WordRelations.fDividedPower_three, Matrix.map_zero _ (map_zero _),
      smul_zero, add_zero]
  simpa only [integralCoordinateOperator_map, adjointMap] using
    EquivarianceIntegration.equivariant_of_integral_commutator integralCoordinateOperator
      (fMatrix (P := typeF4RootPairing) i) (fDividedPower i 2) hFF hBF (hF i)
      t (negativeUnit i t) hg

/-- Integral positive and negative infinitesimal intertwining imply
all-root equivariance over every field, with no characteristic-three exception. -/
theorem rootCurve_equivariant_of_integral_commutators
    (F : Type*) [Field F]
    (hE : PositiveIntegralCommutators) (hF : NegativeIntegralCommutators)
    (r : typeF4Roots) (t : F) :
    Equivariant (adjointMap F) (F4Chevalley.rootCurve r t) :=
  Adjoint.rootCurve_equivariant_of_simple (adjointMap F)
    (positive_simple_equivariant_of_integral_commutators F hE)
    (negative_simple_equivariant_of_integral_commutators F hF) r t

/-- Positive integral commutators and signed opposition suffice for the exact
all-root equivariance premise of the cover-center assembly. -/
theorem rootCurve_equivariant_of_positive_and_opposition
    (F : Type*) [Field F]
    (hE : PositiveIntegralCommutators) (hO : IntegralOppositionCovariance)
    (r : typeF4Roots) (t : F) :
    Equivariant (adjointMap F) (F4Chevalley.rootCurve r t) :=
  rootCurve_equivariant_of_integral_commutators F hE
    (negative_integral_commutators_of_positive_and_opposition hE hO) r t

/-- The fixed signed adjoint map is equivariant under every literal F4 root
curve, including in characteristic three. This discharges the equivariance
premise of `center_eq_bot_of_adjointMap` without any operator hypotheses. -/
theorem rootCurve_equivariant (F : Type*) [Field F]
    (r : typeF4Roots) (t : F) :
    Equivariant (adjointMap F) (F4Chevalley.rootCurve r t) :=
  rootCurve_equivariant_of_positive_and_opposition F
    positive_integral_commutators integral_opposition_covariance r t

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
