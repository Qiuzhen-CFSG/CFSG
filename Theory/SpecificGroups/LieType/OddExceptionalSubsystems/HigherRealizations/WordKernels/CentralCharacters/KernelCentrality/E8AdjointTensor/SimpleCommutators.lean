module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.Candidate

/-!
# Cartan and opposite-simple commutators for the relative E8 tensor

The source bipartite orientation changes the absolute Cartan entries in Geck's
carrier action into signed Cartan integers. The first six E8 nodes have the
literal E6 Cartan matrix, so the E8 Cartan/simple Lie relations prove the tensor
commutators on the source Cartan coordinates. The opposite-simple case is the
normalization built into the tensor.

The orientation calculation and integral descent of the Lie relation follow
`F4Identification.WordDescent.CoverCenter.Equivariance.PositiveCommutators.CartanColumns`.
The relative use here compares two different carriers via `e8Embedding.cartan`.
Source: GLS3 §§1.10–1.12 and 2.6.2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public section
noncomputable section
open scoped Matrix Classical
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
local instance simpleCommutatorsRootFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- Bipartite source signs turn absolute Cartan entries into signed entries. -/
lemma simple_orientation_abs_cartan (i j : typeE6RootPairing_base.support) :
    |typeE6RootPairing_base.cartanMatrix i j| *
        simpleOperatorOrientation (b := typeE6RootPairing_base) i =
      simpleOperatorOrientation (b := typeE6RootPairing_base) j *
        typeE6RootPairing_base.cartanMatrix i j := by
  by_cases hij : i = j
  · subst j
    simp [mul_comm]
  by_cases ha : typeE6RootPairing_base.cartanMatrix i j = 0
  · simp [ha]
  have hs := simpleOperatorOrientation_mul_eq_neg_one_of_cartan_ne_zero i j hij ha
  have hj : simpleOperatorOrientation (b := typeE6RootPairing_base) j =
      -simpleOperatorOrientation (b := typeE6RootPairing_base) i := by
    calc
      _ = (simpleOperatorOrientation (b := typeE6RootPairing_base) i *
          simpleOperatorOrientation (b := typeE6RootPairing_base) i) *
            simpleOperatorOrientation (b := typeE6RootPairing_base) j := by
        rw [simpleOperatorOrientation_sq, one_mul]
      _ = _ := by rw [mul_assoc, hs, mul_neg_one]
  rw [abs_of_nonpos (typeE6RootPairing_base.cartanMatrix_le_zero_of_ne i j hij), hj]
  ring

private lemma integralCartan_e (i j : typeE8RootPairing_base.support) :
    (eMatrix (P := typeE8RootPairing) j * fMatrix j - fMatrix j * eMatrix j) *
        eMatrix i -
      eMatrix i * (eMatrix j * fMatrix j - fMatrix j * eMatrix j) =
        typeE8RootPairing_base.cartanMatrix i j • eMatrix i := by
  apply Matrix.map_injective (FaithfulSMul.algebraMap_injective ℤ ℝ)
  dsimp only
  simp only [Matrix.map_sub _ (map_sub _), Matrix.map_mul,
    Matrix.map_smul _ _ (map_zsmul _ _), map_eMatrix, map_fMatrix]
  have h := RootPairing.GeckConstruction.lie_h_e (P := typeE8RootPairing) i j
  rw [← RootPairing.GeckConstruction.lie_e_f_same j] at h
  exact h

/-- The positive infinitesimal tensor identity on every source Cartan coordinate. -/
lemma positive_commutator_cartan (i j : typeE6RootPairing_base.support) :
    adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ u j) =
      eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * tensor (Sum.inl j) -
        tensor (Sum.inl j) * eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) := by
  rw [eMatrix_mulVec_u, map_smul, adjointMap_single, tensor_simple, tensor_cartan]
  rw [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, ← neg_sub
    ((eMatrix (AdjointBlocks.baseE8 j) * fMatrix (AdjointBlocks.baseE8 j) -
      fMatrix (AdjointBlocks.baseE8 j) * eMatrix (AdjointBlocks.baseE8 j)) *
      eMatrix (AdjointBlocks.baseE8 i))
    (eMatrix (AdjointBlocks.baseE8 i) *
      (eMatrix (AdjointBlocks.baseE8 j) * fMatrix (AdjointBlocks.baseE8 j) -
        fMatrix (AdjointBlocks.baseE8 j) * eMatrix (AdjointBlocks.baseE8 j))),
    integralCartan_e]
  have hc : typeE8RootPairing_base.cartanMatrix (AdjointBlocks.baseE8 i)
      (AdjointBlocks.baseE8 j) = typeE6RootPairing_base.cartanMatrix i j :=
    AdjointBlocks.e8Embedding.cartan i j
  simp only [smul_smul, smul_neg, neg_mul, neg_smul, neg_neg, hc]
  rw [simple_orientation_abs_cartan]

/-- The opposite-simple case is precisely the signed Cartan normalization. -/
lemma positive_commutator_opposite (i : typeE6RootPairing_base.support) :
    let := typeE6RootPairing.indexNeg
    adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ v (b := typeE6RootPairing_base) (-i)) =
      eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) *
          tensor (Sum.inr (-i : typeE6Roots)) -
        tensor (Sum.inr (-i : typeE6Roots)) *
          eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) := by
  let := typeE6RootPairing.indexNeg
  dsimp only
  rw [eMatrix_mulVec_v_neg, adjointMap_single, tensor_neg_simple]
  simp only [tensor_cartan, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- The remaining positive root-coordinate calculation is enough for the full
positive basis contract; Cartan and opposite-simple coordinates are already discharged. -/
theorem positiveCommutators_of_roots
    (hroot : ∀ (i : typeE6RootPairing_base.support) (r : typeE6Roots),
      (let := typeE6RootPairing.indexNeg; r ≠ -(i : typeE6Roots)) →
      adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ v (b := typeE6RootPairing_base) r) =
        eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * tensor (Sum.inr r) -
          tensor (Sum.inr r) * eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)) :
    PositiveCommutators := by
  let := typeE6RootPairing.indexNeg
  intro i j
  rcases j with j | r
  · exact positive_commutator_cartan i j
  · by_cases hr : r = -(i : typeE6Roots)
    · subst r
      exact positive_commutator_opposite i
    · exact hroot i r hr

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
