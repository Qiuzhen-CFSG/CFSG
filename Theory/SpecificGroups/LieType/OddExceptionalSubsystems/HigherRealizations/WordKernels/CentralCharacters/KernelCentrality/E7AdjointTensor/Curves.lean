module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.PositiveCommutators
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.Opposition

/-!
# Integral E7 adjoint covariance on the six numbered root curves

The signed infinitesimal commutator identities imply the polynomial identities
for quadratic root curves. The reused coefficient argument cancels 2 and 3
only over the integers, before specializing to any commutative ring. The
actual E7 cubic coefficient vanishes by `Transport.e7_cubic_zero`.

Source: the common integral lattice in GLS3 §2.6.2; the coefficient argument
is `CoverCenter.Equivariance.Integration`.
-/

@[expose] public section
noncomputable section
open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.WordRelations.Faithfulness
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
attribute [local instance] Classical.decEq
local instance rootsInCurves : Fintype typeE7Roots := Fintype.ofFinite _

/-- Covariance on the full E7 lattice, for each literal six-node curve. -/
theorem numbered_curve_covariance (S : Type*) [CommRing S]
    (a : Bool × Fin 6) (t : S) (x : Coordinate → S) :
    e7Family.curve a t * tensorMap integralCoordinateOperator S x =
      tensorMap integralCoordinateOperator S (e7Family.curve a t *ᵥ x) *
        e7Family.curve a t := by
  have hEE : e7Family.dividedPower a 1 * e7Family.dividedPower a 1 =
      (2 : ℤ) • e7Family.dividedPower a 2 := by
    simpa [Nat.cast_smul_eq_nsmul] using e7Family.mul a 1 1
  have hBE : e7Family.dividedPower a 2 * e7Family.dividedPower a 1 = 0 := by
    simpa [e7_cubic_zero] using e7Family.mul a 2 1
  have hD : ∀ v, integralAdjointMap (e7Family.dividedPower a 1 *ᵥ v) =
      e7Family.dividedPower a 1 * integralAdjointMap v -
        integralAdjointMap v * e7Family.dividedPower a 1 := by
    rcases a with ⟨s, i⟩
    cases s
    · simpa only [e7Family, numberedFamily, simpleFamily, fDividedPower_one] using
        negative_integral_commutators_of_positive positive_integral_commutators
          (typeE7RootPairing_baseEquiv (i.castLE (by decide)))
    · simpa only [e7Family, numberedFamily, simpleFamily, eDividedPower_one] using
        positive_integral_commutators
          (typeE7RootPairing_baseEquiv (i.castLE (by decide)))
  have hg : (e7Family.unit a t).val =
      1 + t • (e7Family.dividedPower a 1).map (Int.castRingHom S) +
        t ^ 2 • (e7Family.dividedPower a 2).map (Int.castRingHom S) := by
    simp only [IntegralCubicFamily.unit_val, IntegralCubicFamily.curve,
      IntegralCubicFamily.coefficient, e7_cubic_zero, Matrix.map_zero _ (map_zero _),
      smul_zero, add_zero]
  exact (F4Identification.CoverCenter.EquivarianceIntegration.equivariant_of_integral_commutator
    integralCoordinateOperator (e7Family.dividedPower a 1) (e7Family.dividedPower a 2)
    hEE hBE hD t (e7Family.unit a t) hg x).symm

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
