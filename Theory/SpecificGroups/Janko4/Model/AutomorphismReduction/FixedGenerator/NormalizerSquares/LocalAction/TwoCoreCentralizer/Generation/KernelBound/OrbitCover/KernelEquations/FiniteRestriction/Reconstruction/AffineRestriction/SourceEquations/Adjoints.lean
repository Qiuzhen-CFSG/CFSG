module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch000
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch005
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch010
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch015
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch020
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch025
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch030
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch035
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch040
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch045
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch050
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch055
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch060
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch065
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch070
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch075
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch080
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.Reconstruction.AffineRestriction.SourceEquations.Adjoints.Batch085

/-!
# All selected adjoint products

The matrices and masks are in the published ATLAS column convention.
See AffineRestriction/source/README.md and SourceEquations/source/README.md.
Generated witness entries are untrusted; the accompanying proofs are checked
by Lean's kernel and use only the displayed mixed-space generators.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
open LinearMembership GeneratorCertificates Binary

theorem adjoint_left_correct (k : Fin 90) :
    rectDecode 12 (pairingAnnihilatorRows.get k) =
      restrictionPairing * (rectDecode 50 (slices 12 50
        (annihilatorMask (adjointWitness.get k)) ))ᵀ := by
  by_cases h0 : k.val < 5
  · simpa only [show 0 + (k.val - 0) = k.val from by omega] using adjoint_left_000 ⟨k.val - 0, by omega⟩
  by_cases h5 : k.val < 10
  · simpa only [show 5 + (k.val - 5) = k.val from by omega] using adjoint_left_005 ⟨k.val - 5, by omega⟩
  by_cases h10 : k.val < 15
  · simpa only [show 10 + (k.val - 10) = k.val from by omega] using adjoint_left_010 ⟨k.val - 10, by omega⟩
  by_cases h15 : k.val < 20
  · simpa only [show 15 + (k.val - 15) = k.val from by omega] using adjoint_left_015 ⟨k.val - 15, by omega⟩
  by_cases h20 : k.val < 25
  · simpa only [show 20 + (k.val - 20) = k.val from by omega] using adjoint_left_020 ⟨k.val - 20, by omega⟩
  by_cases h25 : k.val < 30
  · simpa only [show 25 + (k.val - 25) = k.val from by omega] using adjoint_left_025 ⟨k.val - 25, by omega⟩
  by_cases h30 : k.val < 35
  · simpa only [show 30 + (k.val - 30) = k.val from by omega] using adjoint_left_030 ⟨k.val - 30, by omega⟩
  by_cases h35 : k.val < 40
  · simpa only [show 35 + (k.val - 35) = k.val from by omega] using adjoint_left_035 ⟨k.val - 35, by omega⟩
  by_cases h40 : k.val < 45
  · simpa only [show 40 + (k.val - 40) = k.val from by omega] using adjoint_left_040 ⟨k.val - 40, by omega⟩
  by_cases h45 : k.val < 50
  · simpa only [show 45 + (k.val - 45) = k.val from by omega] using adjoint_left_045 ⟨k.val - 45, by omega⟩
  by_cases h50 : k.val < 55
  · simpa only [show 50 + (k.val - 50) = k.val from by omega] using adjoint_left_050 ⟨k.val - 50, by omega⟩
  by_cases h55 : k.val < 60
  · simpa only [show 55 + (k.val - 55) = k.val from by omega] using adjoint_left_055 ⟨k.val - 55, by omega⟩
  by_cases h60 : k.val < 65
  · simpa only [show 60 + (k.val - 60) = k.val from by omega] using adjoint_left_060 ⟨k.val - 60, by omega⟩
  by_cases h65 : k.val < 70
  · simpa only [show 65 + (k.val - 65) = k.val from by omega] using adjoint_left_065 ⟨k.val - 65, by omega⟩
  by_cases h70 : k.val < 75
  · simpa only [show 70 + (k.val - 70) = k.val from by omega] using adjoint_left_070 ⟨k.val - 70, by omega⟩
  by_cases h75 : k.val < 80
  · simpa only [show 75 + (k.val - 75) = k.val from by omega] using adjoint_left_075 ⟨k.val - 75, by omega⟩
  by_cases h80 : k.val < 85
  · simpa only [show 80 + (k.val - 80) = k.val from by omega] using adjoint_left_080 ⟨k.val - 80, by omega⟩
  simpa only [show 85 + (k.val - 85) = k.val from by omega] using adjoint_left_085 ⟨k.val - 85, by omega⟩

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.Reconstruction.AffineCertificate.SourceEquations
