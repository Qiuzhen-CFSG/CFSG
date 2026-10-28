module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.Model
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.PositiveCommutators.CartanColumns
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.PositiveCommutators.AbsentRoots
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E7AdjointTensor.PositiveCommutators.RootSums

/-!
# Positive-simple commutators of the signed integral E7 adjoint map

The Cartan, opposite-simple, root-sum and absent-root identities cover every
coordinate of the literal 133-dimensional Geck lattice. Linear extension
therefore proves `positive_integral_commutators` with no extra hypotheses.
The canonical root routes and all signs are those fixed by `IntegralModel`.

Together with `Opposition`, this supplies the infinitesimal identities used
by `Curves.numbered_curve_covariance`. Integral polynomial integration and
restriction to the E6 basis finish the tensor construction.
Sources: Geck's integral construction and the GLS3 §§2.2–2.6 conventions.
Adapted from the checked F4 `CoverCenter.Equivariance.PositiveCommutators` proof.
-/

@[expose] public section

open scoped Matrix Classical
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup
open ReeF4.WordRelations.Faithfulness
noncomputable section
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor

attribute [local instance] Classical.decEq
local instance rootsInPositiveCommutators : Fintype typeE7Roots := Fintype.ofFinite _

/-- Positive infinitesimal intertwining on every one of the 133 coordinates. -/
lemma positive_integral_commutator_basis (i : typeE7RootPairing_base.support) (j : Coordinate) :
    integralAdjointMap (eMatrix (P := typeE7RootPairing) i *ᵥ Pi.single j 1) =
      eMatrix i * integralCoordinateOperator j - integralCoordinateOperator j * eMatrix i := by
  let := typeE7RootPairing.indexNeg
  rcases j with j | r
  · exact positive_integral_commutator_cartan i j
  by_cases hopp : r = -(i : typeE7Roots)
  · subst r
    exact positive_integral_commutator_opposite i
  by_cases hsum : typeE7RootPairing.root i + typeE7RootPairing.root r ∈
      Set.range typeE7RootPairing.root
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

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E7AdjointTensor
