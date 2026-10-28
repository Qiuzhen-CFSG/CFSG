module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.IntegralModel
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.CartanColumns
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.AbsentRoots
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.RootSums

/-!
# Positive-simple commutators of the signed integral F4 adjoint map

The Cartan, opposite-simple, root-sum and absent-root identities cover every
coordinate of the literal 52-dimensional Geck lattice. Linear extension
therefore proves `positive_integral_commutators` with no extra hypotheses.
The canonical root routes and all signs are those fixed by `IntegralModel`.

This supplies the integral premise consumed by
`positive_simple_equivariant_of_integral_commutators`; polynomial integration
and the opposition transfer remain in their existing consumer modules.
Sources: Geck's integral construction and the GLS3 §§2.2–2.6 conventions.
-/

public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.CoverCenter

/-- Positive infinitesimal intertwining on every one of the 52 coordinates. -/
lemma positive_integral_commutator_basis (i : typeF4RootPairing_base.support) (j : Coordinate) :
    integralAdjointMap (eMatrix (P := typeF4RootPairing) i *ᵥ Pi.single j 1) =
      eMatrix i * integralCoordinateOperator j - integralCoordinateOperator j * eMatrix i := by
  let := typeF4RootPairing.indexNeg
  rcases j with j | r
  · exact positive_integral_commutator_cartan i j
  by_cases hopp : r = -(i : typeF4Roots)
  · subst r
    exact positive_integral_commutator_opposite i
  by_cases hsum : typeF4RootPairing.root i + typeF4RootPairing.root r ∈
      Set.range typeF4RootPairing.root
  · obtain ⟨s, hs⟩ := hsum
    rw [eMatrix_mulVec_v_add hs, map_smul, integralAdjointMap_single,
      integral_positive_root_commutator_add i r s hs]
  · exact positive_integral_commutator_no_root i r hopp hsum

/-- The fixed signed integral adjoint map intertwines every positive-simple operator. -/
theorem positive_integral_commutators : PositiveIntegralCommutators := by
  intro i x
  have hx : x = ∑ j, x j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  rw [hx]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, map_sum, map_smul,
    integralAdjointMap_single, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun A => x j • A)
    (positive_integral_commutator_basis i j))

end TwistedE6.FoldedSubsystem.F4Identification.CoverCenter
