module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Witnesses

/-!
# Orthogonality coordinate table

The matrices and masks are in the published ATLAS column convention.
See AffineRestriction/source/README.md and SourceEquations/source/README.md.
Generated witness entries are untrusted; the accompanying proofs are checked
by Lean's kernel and use only the displayed mixed-space generators.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
open LinearMembership GeneratorCertificates Binary

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_00 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (0 + j.val) =
      ((mixedGeneratorRows.get ⟨0 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_04 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (4 + j.val) =
      ((mixedGeneratorRows.get ⟨4 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_08 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (8 + j.val) =
      ((mixedGeneratorRows.get ⟨8 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_12 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (12 + j.val) =
      ((mixedGeneratorRows.get ⟨12 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_16 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (16 + j.val) =
      ((mixedGeneratorRows.get ⟨16 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_20 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (20 + j.val) =
      ((mixedGeneratorRows.get ⟨20 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_24 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (24 + j.val) =
      ((mixedGeneratorRows.get ⟨24 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_28 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (28 + j.val) =
      ((mixedGeneratorRows.get ⟨28 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_32 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (32 + j.val) =
      ((mixedGeneratorRows.get ⟨32 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem columns_36 : ∀ (i : Fin 600) (j : Fin 4),
    (mixedColumns.get i).testBit (36 + j.val) =
      ((mixedGeneratorRows.get ⟨36 + j.val, by omega⟩).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val := by decide +kernel

theorem columns_correct (i : Fin 600) (j : Fin 40) :
    bit (mixedColumns.get i) j.val = flat (mixedGenerator j) i := by
  suffices (mixedColumns.get i).testBit j.val =
      ((mixedGeneratorRows.get j).get
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).1).testBit
        ((finProdFinEquiv (m := 12) (n := 50)).symm i).2.val by
    simpa only [bit, flat, mixedGenerator] using congrArg
      (fun b => if b then (1 : ZMod 2) else 0) this
  by_cases h0 : j.val < 4
  · simpa only [show 0 + (j.val - 0) = j.val from by omega] using columns_00 i ⟨j.val - 0, by omega⟩
  by_cases h4 : j.val < 8
  · simpa only [show 4 + (j.val - 4) = j.val from by omega] using columns_04 i ⟨j.val - 4, by omega⟩
  by_cases h8 : j.val < 12
  · simpa only [show 8 + (j.val - 8) = j.val from by omega] using columns_08 i ⟨j.val - 8, by omega⟩
  by_cases h12 : j.val < 16
  · simpa only [show 12 + (j.val - 12) = j.val from by omega] using columns_12 i ⟨j.val - 12, by omega⟩
  by_cases h16 : j.val < 20
  · simpa only [show 16 + (j.val - 16) = j.val from by omega] using columns_16 i ⟨j.val - 16, by omega⟩
  by_cases h20 : j.val < 24
  · simpa only [show 20 + (j.val - 20) = j.val from by omega] using columns_20 i ⟨j.val - 20, by omega⟩
  by_cases h24 : j.val < 28
  · simpa only [show 24 + (j.val - 24) = j.val from by omega] using columns_24 i ⟨j.val - 24, by omega⟩
  by_cases h28 : j.val < 32
  · simpa only [show 28 + (j.val - 28) = j.val from by omega] using columns_28 i ⟨j.val - 28, by omega⟩
  by_cases h32 : j.val < 36
  · simpa only [show 32 + (j.val - 32) = j.val from by omega] using columns_32 i ⟨j.val - 32, by omega⟩
  simpa only [show 36 + (j.val - 36) = j.val from by omega] using columns_36 i ⟨j.val - 36, by omega⟩

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
