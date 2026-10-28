module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.AmbientConditions

/-!
# Actual local elements for restriction normalization

The eleven certified conjugate words of the seed are elements of the ambient
kernel. Their restrictions are the upper-left blocks of the conjugated literal
matrices, and binary products evaluate through the same restriction homomorphism.
This bridge makes a factorization in the ten first-degree coordinates produce
an actual group element.

Source: the ATLAS words and kernel membership in `Cardinality.KernelCount`,
with the adapted-coordinate convention of `KernelBound.Coordinates`.
-/

@[expose] public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
open Coordinates Cardinality.KernelCount

/-- Invertibility of the actual restriction is supplied by group membership. -/
theorem restriction_isUnit (c : SeedCentralizer) : IsUnit (restriction c) :=
  (Group.isUnit c).map restriction

namespace RestrictionRigidity

attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernelSeed

/-- The actual eleven local words, viewed in the ambient kernel. -/
def kernelBasis (i : Fin 11) : ambientKernel :=
  ⟨(basis matrixA_mul_self matrixB_pow_four i : Model),
    ⟨basis matrixA_mul_self matrixB_pow_four i,
      basis_mem_localKernel matrixA_mul_self matrixB_pow_four i, rfl⟩⟩

/-- Evaluation of a local word uses the already certified ATLAS matrix. -/
theorem kernelBasis_matrix (i : Fin 11) :
    toMatrix (kernelBasis i : Model) = decodeRows (basisRows i) :=
  representation_basis matrixA_mul_self matrixB_pow_four i

/-- Literal adapted restriction of each actual local word. -/
theorem restriction_kernelBasis (i : Fin 11) :
    restriction (kernelCentralizerInclusion (kernelBasis i)) =
      restrictionBlock (decodeRows (basisRows i)) := by
  change restrictionBlock (toMatrix (kernelBasis i : Model)) = _
  rw [kernelBasis_matrix]

/-- A binary product is constructed in the actual kernel subtype. -/
def kernelBinaryProduct (v : Fin 11 → Bool) : ambientKernel := binaryProduct kernelBasis v

theorem restriction_kernelBinaryProduct (v : Fin 11 → Bool) :
    restriction (kernelCentralizerInclusion (kernelBinaryProduct v)) =
      binaryProduct (fun i => restrictionBlock (decodeRows (basisRows i))) v := by
  change (restriction.comp kernelCentralizerInclusion) (binaryProduct kernelBasis v) = _
  rw [map_binaryProduct]
  simp only [MonoidHom.comp_apply, restriction_kernelBasis]

end RestrictionRigidity
end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound
