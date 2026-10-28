module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.PackedTable.InputChecks.Traversal

/-!
# Kernel certificates for the packed images

Each candidate form is checked separately to bound kernel reduction. The list-test
soundness theorem then gives the unchanged contract from `Contracts.lean`.
These are unconditional numerical checks of the published source arrays.
Source and ATLAS conventions: `../../../../source/README.md` and
`../source/README.md`.
-/

set_option Elab.async false

public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
open InputChecks

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_000 : ImageCheck 0 :=
  imageTest_sound 0 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_001 : ImageCheck 1 :=
  imageTest_sound 1 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_002 : ImageCheck 2 :=
  imageTest_sound 2 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_003 : ImageCheck 3 :=
  imageTest_sound 3 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_004 : ImageCheck 4 :=
  imageTest_sound 4 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_005 : ImageCheck 5 :=
  imageTest_sound 5 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_006 : ImageCheck 6 :=
  imageTest_sound 6 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_007 : ImageCheck 7 :=
  imageTest_sound 7 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_008 : ImageCheck 8 :=
  imageTest_sound 8 (by decide +kernel)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem checked_images_009 : ImageCheck 9 :=
  imageTest_sound 9 (by decide +kernel)

/-- Every published candidate form satisfies its packed input contract. -/
theorem images_checked : ∀ i : Fin 10, ImageCheck i := by
  intro i
  fin_cases i
  · exact checked_images_000
  · exact checked_images_001
  · exact checked_images_002
  · exact checked_images_003
  · exact checked_images_004
  · exact checked_images_005
  · exact checked_images_006
  · exact checked_images_007
  · exact checked_images_008
  · exact checked_images_009

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients.PackedTable
