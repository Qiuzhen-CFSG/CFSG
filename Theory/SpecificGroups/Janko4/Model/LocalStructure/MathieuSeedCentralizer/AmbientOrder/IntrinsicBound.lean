module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound
public import Theory.Representation.BinaryQuarticMathieu
public import Mathlib.GroupTheory.Index


/-!
# The intrinsic action bounds the full seed centralizer

The independent intrinsic-algebra and full-kernel constructions use the same
adapted basis and concrete algebra. Their inverse matrices and algebra basis
words agree definitionally; uniqueness of inverses identifies the adapted
bases. The upper-left block conventions then give the same restriction map.

The kernel of the actual ten-dimensional action therefore embeds in the
known local kernel of order 2048. Its image in the literal quartic stabilizer
has order at most 887040 by the faithful action on the marked Witt design.
The kernel-image formula uses this same action of the full ambient centralizer.
All coordinate and invariance premises are discharged; no ambient order,
simplicity, max1 containment, or centralizer-generation premise is used.

Source motivation: GLS3 Table 5.3i, printed p.270. The matrix and tensor
certificates are documented in the sibling `IntrinsicAlgebra/source/README.md`,
`KernelBound/source/README.md`, and
`Theory/Representation/BinaryQuarticMathieu/source/README.md`.
-/

public section

open scoped Matrix

namespace Janko4.LocalStructure.MathieuSeedCentralizer
namespace AmbientOrder
namespace Calibration
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernelSeed

/-- The two saved inverse matrices have literally identical rows. -/
theorem adaptedInverse_eq :
    IntrinsicAlgebra.adaptedInverse = KernelBound.Coordinates.adaptedBasisInverse := rfl

attribute [local irreducible] IntrinsicAlgebra.adaptedMatrix IntrinsicAlgebra.adaptedInverse
  KernelBound.Coordinates.adaptedBasis KernelBound.Coordinates.adaptedBasisInverse

/-- Uniqueness of inverses reconciles the column and row basis encodings. -/
theorem adaptedMatrix_eq :
    IntrinsicAlgebra.adaptedMatrix = KernelBound.Coordinates.adaptedBasis := by
  have h : IntrinsicAlgebra.adaptedInverse * KernelBound.Coordinates.adaptedBasis = 1 := by
    rw [adaptedInverse_eq]
    simpa only [KernelBound.Coordinates.adaptedBasisInverse,
      KernelBound.Coordinates.adaptedBasis] using KernelBound.Coordinates.adapted_inverse_mul
  exact left_inv_eq_right_inv (M := BinaryMatrix)
    (a := IntrinsicAlgebra.adaptedInverse) (b := IntrinsicAlgebra.adaptedMatrix)
    (c := KernelBound.Coordinates.adaptedBasis) IntrinsicAlgebra.adaptedMatrix_mul_adaptedInverse h

/-- Both constructions decode the same 56 algebra basis words. -/
theorem algebraBasis_eq :
    IntrinsicAlgebra.algebraBasis = KernelBound.Coordinates.algebraBasis := rfl

theorem algebraSpan_eq :
    IntrinsicAlgebra.algebraSpan = KernelBound.Coordinates.concreteAlgebra := rfl

private theorem blockReindex_upper (M : BinaryMatrix) :
    (KernelBound.Coordinates.blockReindex M).toBlocks₁₁ =
      M.submatrix IntrinsicAlgebra.firstIndex IntrinsicAlgebra.firstIndex := by
  ext i j
  rfl

/-- The submatrix and sum-index upper-left block conventions agree. -/
theorem restrictionBlock_eq (g : BinaryMatrix) :
    IntrinsicAlgebra.restrictionBlock g = KernelBound.Coordinates.restrictionBlock g := by
  unfold IntrinsicAlgebra.restrictionBlock KernelBound.Coordinates.restrictionBlock
    KernelBound.Coordinates.blockCoordinates KernelBound.Coordinates.conjugateMatrix
  rw [blockReindex_upper]
  exact congrArg (fun M : BinaryMatrix =>
    M.submatrix IntrinsicAlgebra.firstIndex IntrinsicAlgebra.firstIndex)
      (congrArg₂ (fun P Q : BinaryMatrix => P * g * Q) adaptedInverse_eq adaptedMatrix_eq)

/-- The intrinsic kernel certificate supplies the exact full-kernel premise. -/
theorem restriction_mem_of_mem_rho_ker (c : IntrinsicAlgebra.centralizer)
    (hc : c ∈ IntrinsicAlgebra.rho.ker) :
    KernelBound.restriction c ∈ KernelBound.Coordinates.concreteAlgebra := by
  change KernelBound.Coordinates.restrictionBlock (toMatrix (c : Model)) ∈ _
  rw [← restrictionBlock_eq, ← algebraSpan_eq]
  exact IntrinsicAlgebra.restrictionBlock_mem_algebraSpan_of_mem_rho_ker c hc

end Calibration

/-- Every element of the full intrinsic action kernel lies in the known local kernel. -/
theorem mem_ambientKernel_of_mem_rho_ker (c : IntrinsicAlgebra.centralizer)
    (hc : c ∈ IntrinsicAlgebra.rho.ker) :
    (c : Model) ∈ KernelBound.ambientKernel :=
  KernelBound.mem_ambientKernel_of_restriction_mem c
    (Calibration.restriction_mem_of_mem_rho_ker c hc)

/-- Faithful inclusion in the actual local kernel bounds all intrinsic kernel elements. -/
theorem rho_ker_card_le : Nat.card IntrinsicAlgebra.rho.ker ≤ 2048 := by
  let f : IntrinsicAlgebra.rho.ker → KernelBound.ambientKernel :=
    fun c => ⟨c.val, mem_ambientKernel_of_mem_rho_ker c.val c.property⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : KernelBound.ambientKernel => (z : Model)) h
  simpa only [KernelBound.ambientKernel_card] using Nat.card_le_card_of_injective f hf

/-- Passing to the literal quartic stabilizer preserves the action kernel. -/
theorem quarticAction_ker_card_le :
    Nat.card IntrinsicAlgebra.rhoToQuarticStabilizer.ker ≤ 2048 := by
  rw [IntrinsicAlgebra.rhoToQuarticStabilizer_ker]
  exact rho_ker_card_le

/-- The image of the full centralizer is bounded by the full quartic stabilizer. -/
theorem quarticAction_range_card_le :
    Nat.card IntrinsicAlgebra.rhoToQuarticStabilizer.range ≤ 887040 := by
  have : Finite BinaryQuarticMathieu.quarticStabilizer :=
    Finite.of_injective _ BinaryQuarticMathieu.quarticDesignAction_injective
  exact (Nat.card_le_card_of_injective _
    (Subtype.val_injective (p := fun g => g ∈ IntrinsicAlgebra.rhoToQuarticStabilizer.range))).trans
      BinaryQuarticMathieu.quarticStabilizer_card_le

/-- The kernel-image formula for the same calibrated full-centralizer action. -/
theorem card_centralizer_eq_quartic_kernel_mul_image :
    Nat.card IntrinsicAlgebra.centralizer =
      Nat.card IntrinsicAlgebra.rhoToQuarticStabilizer.ker *
        Nat.card IntrinsicAlgebra.rhoToQuarticStabilizer.range := by
  rw [← IntrinsicAlgebra.rhoToQuarticStabilizer.ker.card_mul_index, Subgroup.index_ker]

end AmbientOrder
end Janko4.LocalStructure.MathieuSeedCentralizer
