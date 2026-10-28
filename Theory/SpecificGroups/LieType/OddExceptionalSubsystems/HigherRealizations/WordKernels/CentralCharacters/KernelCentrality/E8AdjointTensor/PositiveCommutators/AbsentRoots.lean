module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.PositiveCommutators.RootSums
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.AdjointEquivariance.PositiveSimple.RootLinear.NoRootSums

/-!
# Absent-root commutators for the relative E6 tensor in E8

Saturation of the literal root embedding transfers absence of a source root
sum to E8. The sum is nonzero outside the opposite-simple case. The integral
absent-weight theorem then kills the commutator, including for negative roots,
using the signed positive-simple transport of the fixed source tensor.

This is the absent-root branch of `PositiveCommutators`. Adapted from the F4
`CoverCenter.Equivariance.PositiveCommutators.AbsentRoots` proof.
Source: GLS3 §§1.10–1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Classical
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Saturation rules out an ambient root when the source sum is absent. -/
lemma embedded_no_sum (i : typeE6RootPairing_base.support) (r : typeE6Roots)
    (hsum : typeE6RootPairing.root i + typeE6RootPairing.root r ∉
      Set.range typeE6RootPairing.root) :
    typeE8RootPairing.root (AdjointBlocks.baseE8 i) +
      typeE8RootPairing.root (AdjointBlocks.rootE8 r) ∉ Set.range typeE8RootPairing.root := by
  intro h
  apply hsum
  apply AdjointBlocks.e8Embedding.saturated
  simpa only [map_add, embedded_root, embedded_base] using h

/-- The actual relative root tensor commutes with a simple operator if the
nonzero sum is absent from the saturated E6 subsystem. -/
lemma positive_root_commutator_zero (i : typeE6RootPairing_base.support) (r : typeE6Roots)
    (hopp : let := typeE6RootPairing.indexNeg; r ≠ -(i : typeE6Roots))
    (hsum : typeE6RootPairing.root i + typeE6RootPairing.root r ∉
      Set.range typeE6RootPairing.root) :
    eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * rootTensor r -
      rootTensor r * eMatrix (AdjointBlocks.baseE8 i) = 0 := by
  let := typeE6RootPairing.indexNeg
  have h0 : typeE6RootPairing.root i + typeE6RootPairing.root r ≠ 0 := by
    intro h
    apply hopp
    apply typeE6RootPairing.root.injective
    simpa only [RootPairing.indexNeg_neg, typeE6RootPairing.root_reflectionPerm,
      typeE6RootPairing.reflection_apply_self] using eq_neg_of_add_eq_zero_right h
  have h0' : typeE8RootPairing.root (AdjointBlocks.baseE8 i) +
      typeE8RootPairing.root (AdjointBlocks.rootE8 r) ≠ 0 := by
    intro h
    apply h0
    apply AdjointBlocks.e8Embedding.injective
    simpa only [map_add, map_zero, embedded_root, embedded_base] using h
  obtain ⟨w, j, q, _, hw, hr⟩ := rootTensor_eq_signed_transport r
  have hc := integral_commutator_zero (P := typeE8RootPairing)
    (AdjointBlocks.baseE8 i) j w (by simpa only [hw] using h0')
    (by simpa only [hw] using embedded_no_sum i r hsum)
  rw [hr, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, hc, smul_zero]

/-- The positive tensor identity on the absent-root branch. -/
lemma positive_commutator_no_root (i : typeE6RootPairing_base.support) (r : typeE6Roots)
    (hopp : let := typeE6RootPairing.indexNeg; r ≠ -(i : typeE6Roots))
    (hsum : typeE6RootPairing.root i + typeE6RootPairing.root r ∉
      Set.range typeE6RootPairing.root) :
    adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ v (b := typeE6RootPairing_base) r) =
      eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * tensor (Sum.inr r) -
        tensor (Sum.inr r) * eMatrix (AdjointBlocks.baseE8 i) := by
  rw [eMatrix_mulVec_v_zero hopp hsum, map_zero]
  exact (positive_root_commutator_zero i r hopp hsum).symm

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
