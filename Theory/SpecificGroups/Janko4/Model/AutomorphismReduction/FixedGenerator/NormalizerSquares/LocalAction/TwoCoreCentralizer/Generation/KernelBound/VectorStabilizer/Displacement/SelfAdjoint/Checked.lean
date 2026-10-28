module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.SelfAdjoint.Witnesses

/-!
# Checked self-adjoint coefficient data

Every product and transpose identity concerns all rows of the actual matrices.
The selected coefficient rows have a complete recovery certificate, and each
kernel column vanishes on the full image. The last combination check identifies
the published 45 matrices. These are ordinary kernel computations, isolated
from the algebraic transport to avoid repeating them during elaboration.
See source/README.md for reproduction and the exact finite contract.
-/

public section
set_option Elab.async false
set_option maxRecDepth 10000
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra

namespace SelfAdjointCertificate

set_option maxHeartbeats 5000000 in
theorem product_checks : ∀ k : Fin 102, ∀ i : Fin 50,
    scan (restrictionPairingRows.get i) (slices 50 50 (nilWords.get k)).toList =
      (productWords.get k >>> (50 * i.val)) % 2^50 := by
  simp only [slices, Vector.toList_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem image_checks : ∀ k : Fin 102, ∀ i : Fin 50,
    (slices 50 50 (imageWords.get k)).get i =
      (transRows 50 (slices 50 50 (productWords.get k))).get i ^^^
        (slices 50 50 (productWords.get k)).get i := by
  simp only [slices, transRows, get_ofFn]
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem evaluation_checks : ∀ i : Fin 57, ∀ k : Fin 102,
    (evaluationRows.get i).testBit k.val =
      (imageWords.get k).testBit ((columnIndices.get i).val + 50 * (rowIndices.get i).val) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem recovery_checks : ∀ i : Fin 102,
    scan (recoveryRows.get i) evaluationRows.toList = remainderRows.get i := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem remainder_checks : ∀ i : Fin 102,
    remainderRows.get i = 2 ^ i.val ^^^
      xorList (List.ofFn (fun k : Fin 45 =>
        if (selfAdjointKernelWords.get k).testBit i.val
        then 2 ^ (freeIndices.get k).val else 0)) := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem combination_checks : ∀ k : Fin 45,
    scan (selfAdjointKernelWords.get k) nilWords.toList = selfAdjointWords.get k := by
  decide +kernel

set_option maxHeartbeats 5000000 in
theorem kernel_checks : ∀ k : Fin 45,
    scan (selfAdjointKernelWords.get k) imageWords.toList = 0 := by
  decide +kernel

end SelfAdjointCertificate
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement
