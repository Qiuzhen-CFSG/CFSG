module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.Candidate
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.KernelCentrality.E8AdjointTensor.Integration

/-!
# Signed opposition transfers the relative positive commutators

Positive infinitesimal covariance and the signed opposition identity imply
negative infinitesimal covariance for the same integral tensor. Source and
target opposition act on different lattices; each exchanges the corresponding
raising and lowering operators. This is the relative form of the transfer in
`F4Identification.WordDescent.CoverCenter.Equivariance.IntegralModel`.

Both mathematical inputs remain explicit. The E8 data assembly consumes the
negative identities from this theorem. Source: GLS3 §§1.12 and 2.6.2.
-/

public section
noncomputable section
open Matrix Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
attribute [local instance] Classical.decEq
local instance oppositionTransferRootFintype : Fintype typeE8Roots := Fintype.ofFinite _

/-- Positive basis commutators act on every integral vector. -/
lemma positive_commutator_linear (hE : PositiveCommutators)
    (i : typeE6RootPairing_base.support) (x : Index → ℤ) :
    adjointMap (eMatrix (P := typeE6RootPairing) i *ᵥ x) =
      eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) * adjointMap x -
        adjointMap x * eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i) := by
  apply commutator_of_basis
  intro j
  simpa only [adjointMap_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hE i j

/-- Positive commutators and actual signed opposition discharge the negative contract. -/
theorem negativeCommutators_of_positive_and_opposition
    (hE : PositiveCommutators) (hO : IntegralOppositionCovariance) :
    NegativeCommutators := by
  intro i j
  let x : Index → ℤ := Pi.single j 1
  let O := omegaMatrix (P := typeE6RootPairing) (b := typeE6RootPairing_base)
  let O' := omegaMatrix (P := typeE8RootPairing) (b := typeE8RootPairing_base)
  let E := eMatrix (P := typeE6RootPairing) i
  let N := fMatrix (P := typeE6RootPairing) i
  let E' := eMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)
  let N' := fMatrix (P := typeE8RootPairing) (AdjointBlocks.baseE8 i)
  have hOO : O * O = 1 := omegaMatrix_sq
  have hOO' : O' * O' = 1 := omegaMatrix_sq
  have hOE : O * E = N * O := omegaMatrix_mul_eMatrix i
  have hOE' : O' * E' = N' * O' := omegaMatrix_mul_eMatrix (AdjointBlocks.baseE8 i)
  have hvec : O *ᵥ (E *ᵥ (O *ᵥ x)) = N *ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hOE, mul_assoc, hOO, mul_one]
  have hx : adjointMap x = tensor j := adjointMap_single j
  change adjointMap (N *ᵥ x) = N' * tensor j - tensor j * N'
  rw [← hx]
  calc
    _ = -(O' * adjointMap (E *ᵥ (O *ᵥ x)) * O') := by
      have h := hO (E *ᵥ (O *ᵥ x))
      change adjointMap (O *ᵥ (E *ᵥ (O *ᵥ x))) = _ at h
      rw [hvec] at h
      exact h
    _ = (O' * E') * O' * adjointMap x * (O' * O') -
        (O' * O') * adjointMap x * (O' * E') * O' := by
      rw [positive_commutator_linear hE i, hO x]
      change -(O' * (E' * -(O' * adjointMap x * O') -
        -(O' * adjointMap x * O') * E') * O') = _
      noncomm_ring
    _ = _ := by
      rw [hOE', hOO']
      simp only [one_mul, mul_one, mul_assoc, hOO']

end TwistedE6.FoldedSubsystem.HigherRealizations.KernelCentrality.E8AdjointTensor
