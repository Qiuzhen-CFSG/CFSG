module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedKernel.LinearConstraints

/-!
# Assembly of the full seed fixed-space kernel bound

The full ambient action kernel satisfies explicit linear conditions obtained
from two ambient exterior forms. Two independent finite certificates remain:
the mixed-restriction upper bound and the scalar rigidity of that linear
system. Once both are supplied, every kernel actor is the identity or the
literal seed, giving the required cardinality bound two.

This module proves the assembly only; the unconditional theorem
`fixedAction_kernel_card_le` is not asserted until those certificates are
proved. Source motivation: GLS3 Table 5.3i; literal words and matrices:
`Cardinality.Subgroup` and `Cardinality.LocalOrder.KernelCount.Relations`.
-/

set_option maxRecDepth 2048

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder

open SeedKernel
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
  (exteriorFormSpace)

attribute [local irreducible] modelGroup matrixA matrixB fixedAction naturalAction
  Cardinality.localKernelSeed Cardinality.max1Subgroup

/-- Convert finite linear-system rigidity into the exact full-kernel dichotomy.
Both additional premises must be discharged before using this as an ambient
kernel bound. -/
theorem fixedAction_kernel_eq_one_or_seed_of_linear_certificates
    (hrestriction : ∀ R ∈ exteriorFormSpace, fixedRestriction R = 0 →
      crossRestriction R ∈ candidateCrossSpace)
    (hrigidity : ∀ D : BinaryMatrix, LinearConditions D →
      D = 0 ∨ D = seedMatrixDisplacement)
    (c : fixedAction.ker) : c.val = 1 ∨ c.val = markedSeed := by
  rcases hrigidity _ (kernel_linearConditions hrestriction c) with h | h
  · left
    apply Subtype.ext
    apply toMatrix_injective
    simpa only [OneMemClass.coe_one, map_one] using sub_eq_zero.mp h
  · right
    apply Subtype.ext
    apply toMatrix_injective
    change toMatrix (c.val : Model) = toMatrix seed
    simpa only [seedMatrixDisplacement, sub_add_cancel] using
      congrArg (fun D : BinaryMatrix => D + 1) h

/-- The two finite linear certificates suffice for the required full ambient
kernel cardinality bound. -/
theorem fixedAction_kernel_card_le_of_linear_certificates
    (hrestriction : ∀ R ∈ exteriorFormSpace, fixedRestriction R = 0 →
      crossRestriction R ∈ candidateCrossSpace)
    (hrigidity : ∀ D : BinaryMatrix, LinearConditions D →
      D = 0 ∨ D = seedMatrixDisplacement) : Nat.card fixedAction.ker ≤ 2 := by
  classical
  let f : fixedAction.ker → Bool := fun c => decide (c.val = 1)
  have hf : Function.Injective f := by
    intro c d h
    have hsame : (c.val = 1) ↔ (d.val = 1) := decide_eq_decide.mp h
    apply Subtype.ext
    rcases fixedAction_kernel_eq_one_or_seed_of_linear_certificates
      hrestriction hrigidity c with hc | hc
    · have hd : d.val = 1 := hsame.mp hc
      exact hc.trans hd.symm
    · rcases fixedAction_kernel_eq_one_or_seed_of_linear_certificates
        hrestriction hrigidity d with hd | hd
      · have hc' : c.val = 1 := hsame.mpr hd
        exact hc'.trans hd.symm
      · exact hc.trans hd.symm
  simpa using Nat.card_le_card_of_injective f hf

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder
