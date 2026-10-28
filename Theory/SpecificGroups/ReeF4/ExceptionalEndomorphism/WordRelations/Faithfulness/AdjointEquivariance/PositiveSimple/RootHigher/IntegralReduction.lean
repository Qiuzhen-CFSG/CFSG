module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.Coefficients
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.RouteComparison

/-!
# Reducing the quadratic coefficient to an integral operator comparison

The second divided power of the adjoint action on a root operator is
`B A - E A E + A B`. The second vector column supplies a second integral
matrix by linear extension of the actual routed root operators. Equality after
specialization to characteristic two, together with the degree-one identity
and `E² = 0`, gives degree two. Agreement up to an integral sign is a stronger
sufficient condition, retained as a separate interface.

This module defines both matrices independently and proves only the
specialization step. Their signed comparison is a separate mathematical
obligation. All integral matrices use the normalization of
`IntegralGeckConstruction` and `IntegralAllRootOperators`; sign elimination
uses `Intertwining.Transport.RouteComparison`.
-/

@[expose] public section

open scoped Matrix
open Theory.AlgebraicGroup StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
noncomputable section
/-- The integral second adjoint divided power on the actual routed root operator. -/
def integralQuadraticOperator (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    Matrix Coordinate Coordinate ℤ :=
  eDividedPower (P := typeF4RootPairing) i 2 * F4Chevalley.integralOperators.rootOperator r -
    eMatrix i * F4Chevalley.integralOperators.rootOperator r * eMatrix i +
    F4Chevalley.integralOperators.rootOperator r * eDividedPower i 2

/-- Apply the actual integral root operators to the second divided-power column.
Cartan coordinates do not occur in a second divided-power column. -/
def integralQuadraticColumn (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    Matrix Coordinate Coordinate ℤ :=
  ∑ s : typeF4Roots, eDividedPower (P := typeF4RootPairing) i 2 (Sum.inr s) (Sum.inr r) •
    F4Chevalley.integralOperators.rootOperator s

lemma map_integralQuadraticOperator (m : ℕ) (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
      dividedPower m i 2 * coordinateOperator m (Sum.inr r) -
        dividedPower m i 1 * coordinateOperator m (Sum.inr r) * dividedPower m i 1 +
        coordinateOperator m (Sum.inr r) * dividedPower m i 2 := by
  simp only [integralQuadraticOperator, Matrix.map_add _ (map_add _),
    Matrix.map_sub _ (map_sub _), Matrix.map_mul, dividedPower, coordinateOperator,
    eDividedPower_one]

lemma map_integralQuadraticColumn (m : ℕ) (i : typeF4RootPairing_base.support) (r : typeF4Roots) :
    (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m)) =
      columnImage m i 2 (Sum.inr r) := by
  classical
  ext x y
  simp only [integralQuadraticColumn, Matrix.map_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp [columnImage, adjointMap, linearExtension, Fintype.sum_sum_type,
    dividedPower, eDividedPower, coordinateOperator, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> simp

/-- Equality of the specialized quadratic operators supplies degree two;
no integral sign comparison is required. Degree one stays explicit. -/
lemma coefficientIdentity_two_of_integral_map_eq (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) (h1 : CoefficientIdentity m i (Sum.inr r) 1)
    (hcast : (integralQuadraticOperator i r).map (Int.castRingHom (CoefficientField m)) =
      (integralQuadraticColumn i r).map (Int.castRingHom (CoefficientField m))) :
    CoefficientIdentity m i (Sum.inr r) 2 := by
  rw [map_integralQuadraticOperator, map_integralQuadraticColumn] at hcast
  have hU := (coefficientIdentity_one_iff m i (Sum.inr r)).mp h1
  unfold CoefficientIdentity curveProductCoefficient
  rw [← hcast, hU]
  have hEE : dividedPower m i 1 * dividedPower m i 1 = 0 := by
    have h := dividedPower_mul m i 1 1
    rw [← Nat.cast_smul_eq_nsmul (CoefficientField m)] at h
    change _ = (2 : CoefficientField m) • dividedPower m i 2 at h
    simpa only [CharTwo.two_eq_zero, zero_smul] using h
  simp only [sub_mul, mul_assoc, hEE, mul_zero, sub_zero]
  have hadd (A : Matrix Coordinate Coordinate (CoefficientField m)) : A + A = 0 := by
    ext x y
    exact CharTwo.add_self_eq_zero _
  calc
    _ = dividedPower m i 2 * coordinateOperator m (Sum.inr r) +
        (coordinateOperator m (Sum.inr r) * dividedPower m i 2 +
          coordinateOperator m (Sum.inr r) * dividedPower m i 2) := by abel
    _ = _ := by rw [hadd, add_zero]

/-- A signed integral comparison supplies degree two; degree one stays explicit. -/
lemma coefficientIdentity_two_of_integral_sign (m : ℕ) (i : typeF4RootPairing_base.support)
    (r : typeF4Roots) (h1 : CoefficientIdentity m i (Sum.inr r) 1)
    (hIntegral : ∃ ε : ℤ, ε ^ 2 = 1 ∧
      integralQuadraticOperator i r = ε • integralQuadraticColumn i r) :
    CoefficientIdentity m i (Sum.inr r) 2 := by
  obtain ⟨ε, hε, h⟩ := hIntegral
  exact coefficientIdentity_two_of_integral_map_eq m i r h1
    (RouteComparison.map_eq_of_sign_smul (S := CoefficientField m)
      (integralQuadraticOperator i r) (integralQuadraticColumn i r) ε 1 hε (by simpa using h))
end
end ReeF4.WordRelations.Faithfulness.Adjoint.PositiveSimple
