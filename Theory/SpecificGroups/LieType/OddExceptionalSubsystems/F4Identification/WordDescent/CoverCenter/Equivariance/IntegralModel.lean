module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Operators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.Integration

/-!
# Integral form of the fixed signed F4 adjoint map

The root coordinates use exactly `rootOperatorOrientation` and the canonical
root operators of `Operators`. The Cartan coordinates are the negative
simple orientation times the integral raising/lowering commutator.
Specialization recovers the fixed `coordinateOperator` and `adjointMap`, with
no change to their signs, routes, or coordinate carrier.

The two infinitesimal contracts concern actual matrix commutators on this
integral lattice. Signed opposition covariance transports the positive
identity to the negative identity. These contracts contain neither group
equivariance nor injectivity; `Equivariance` proves the divided-power
integration and all-root application.
Sources: `IntegralChevalleyOperatorOrientation`, `IntegralGeckConstruction`,
and the adjoint construction in GLS3 §§2.2–2.6.
-/

@[expose] public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

/-- The signed adjoint coordinate family before changing coefficients. -/
def integralCoordinateOperator : Coordinate → Matrix Coordinate Coordinate ℤ
  | Sum.inr r => rootOperatorOrientation r •
      rootOperator (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  | Sum.inl i => -simpleOperatorOrientation (b := typeF4RootPairing_base) i •
      (eMatrix (P := typeF4RootPairing) i * fMatrix i - fMatrix i * eMatrix i)

/-- The integral form of the fixed signed adjoint map. -/
def integralAdjointMap : (Coordinate → ℤ) →ₗ[ℤ] Matrix Coordinate Coordinate ℤ :=
  Adjoint.linearExtension integralCoordinateOperator

lemma integralAdjointMap_single (j : Coordinate) :
    integralAdjointMap (Pi.single j 1) = integralCoordinateOperator j :=
  Adjoint.linearExtension_single _ _

lemma integralCoordinateOperator_map (F : Type*) [Field F] (j : Coordinate) :
    (integralCoordinateOperator j).map (Int.castRingHom F) = coordinateOperator F j := by
  rcases j with i | r
  · simp only [integralCoordinateOperator, coordinateOperator,
      Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul F,
      Int.cast_neg, Matrix.map_sub _ (map_sub _), Matrix.map_mul]
  · simp only [integralCoordinateOperator, coordinateOperator, specializedRootOperator,
      Matrix.map_smul _ _ (map_zsmul _ _), ← Int.cast_smul_eq_zsmul F]

lemma integralAdjointMap_map (F : Type*) [Field F] (v : Coordinate → ℤ) :
    (integralAdjointMap v).map (Int.castRingHom F) =
      adjointMap F ((Int.castRingHom F) ∘ v) := by
  simpa only [integralAdjointMap, adjointMap, integralCoordinateOperator_map] using
    EquivarianceIntegration.map_linearExtension (K := F) integralCoordinateOperator v

/-- The infinitesimal positive-simple intertwining contract. -/
def PositiveIntegralCommutators : Prop :=
  ∀ (i : typeF4RootPairing_base.support) (v : Coordinate → ℤ),
    integralAdjointMap (eMatrix (P := typeF4RootPairing) i *ᵥ v) =
      eMatrix i * integralAdjointMap v - integralAdjointMap v * eMatrix i

/-- The infinitesimal negative-simple intertwining contract. -/
def NegativeIntegralCommutators : Prop :=
  ∀ (i : typeF4RootPairing_base.support) (v : Coordinate → ℤ),
    integralAdjointMap (fMatrix (P := typeF4RootPairing) i *ᵥ v) =
      fMatrix i * integralAdjointMap v - integralAdjointMap v * fMatrix i

/-- Opposition acts on adjoint operators with the sign forced by
`D(vᵢ) = εᵢEᵢ` and `D(v₋ᵢ) = -εᵢFᵢ`. -/
def IntegralOppositionCovariance : Prop :=
  ∀ v : Coordinate → ℤ,
    integralAdjointMap
      (omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base) *ᵥ v) =
    -(omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base) *
      integralAdjointMap v * omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base))

/-- Signed opposition and positive infinitesimal intertwining give the
negative infinitesimal identity for the same fixed map. -/
theorem negative_integral_commutators_of_positive_and_opposition
    (hE : PositiveIntegralCommutators) (hO : IntegralOppositionCovariance) :
    NegativeIntegralCommutators := by
  intro i v
  let O := omegaMatrix (P := typeF4RootPairing) (b := typeF4RootPairing_base)
  let E := eMatrix (P := typeF4RootPairing) i
  let N := fMatrix (P := typeF4RootPairing) i
  have hOO : O * O = 1 := omegaMatrix_sq
  have hOE : O * E = N * O := omegaMatrix_mul_eMatrix i
  have hvec : O *ᵥ (E *ᵥ (O *ᵥ v)) = N *ᵥ v := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hOE, mul_assoc, hOO, mul_one]
  change integralAdjointMap (N *ᵥ v) = N * integralAdjointMap v - integralAdjointMap v * N
  calc
    _ = -(O * integralAdjointMap (E *ᵥ (O *ᵥ v)) * O) := by
      have h := hO (E *ᵥ (O *ᵥ v))
      change integralAdjointMap (O *ᵥ (E *ᵥ (O *ᵥ v))) = _ at h
      rw [hvec] at h
      exact h
    _ = (O * E) * O * integralAdjointMap v * (O * O) -
        (O * O) * integralAdjointMap v * (O * E) * O := by
      rw [hE i, hO v]
      change -(O * (E * -(O * integralAdjointMap v * O) -
        -(O * integralAdjointMap v * O) * E) * O) = _
      noncomm_ring
    _ = _ := by
      rw [hOE, hOO]
      simp only [one_mul, mul_one, mul_assoc, hOO]

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

