module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity.Definitions
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.Arithmetic

/-!
# Calibration of both shear test forms

The original exterior combination masks certify membership in the complete W.
Two packed products compute Pᵀ F P with the actual shared P. Their upper-left
blocks are exactly R₀ and R₁, so the ambient shear constraint applies to both
literal tests. No dimension or completeness claim about W is required here.

Source: the reproduced two-test witness described in `source/README.md`.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
open Coordinates GeneratorCertificates
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates
open LinearMembership RadicalCertificate

private def ambientRows (t : Fin 2) : Vector ℕ 112 :=
  if t = 0 then testAmbientRows0 else testAmbientRows1

private def leftRows (t : Fin 2) : Vector ℕ 112 :=
  if t = 0 then testLeftRows0 else testLeftRows1

private def transportedRows (t : Fin 2) : Vector ℕ 112 :=
  if t = 0 then testAdaptedRows0 else testAdaptedRows1

private def FormChecks (t : Fin 2) : Prop :=
  scan (testCoefficients.get t) exteriorFormRows.toList = testFormWords.get t ∧
  (∀ i j : Fin 112, ((ambientRows t).get i).testBit j.val =
    if i < j then (testFormWords.get t).testBit (exteriorIndex i j)
    else if j < i then (testFormWords.get t).testBit (exteriorIndex j i) else false) ∧
  (∀ i : Fin 112, packedRow (adaptedTransposeRows.get i) (ambientRows t) =
    (leftRows t).get i) ∧
  (∀ i : Fin 112, packedRow ((leftRows t).get i) adaptedRows =
    (transportedRows t).get i) ∧
  upperBlockLinear (blockReindex (decodeRows (transportedRows t))) = testRestriction t

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked0 : FormChecks 0 := by
  unfold FormChecks
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked1 : FormChecks 1 := by
  unfold FormChecks
  decide +kernel

private theorem formChecks (t : Fin 2) : FormChecks t := by
  fin_cases t
  · exact checked0
  · exact checked1

attribute [local irreducible] testFormWords testCoefficients ambientRows leftRows
  transportedRows exteriorFormRows

/-- Both displayed forms belong to the actual transported exterior space. -/
theorem testForm_mem (t : Fin 2) : testForm t ∈ adaptedExteriorSpace := by
  refine ⟨decodeExteriorForm (testFormWords.get t), ?_, rfl⟩
  rw [← (formChecks t).1, scan_eq, decodeExteriorForm_combination]
  exact exteriorFormSpace.sum_mem (fun i _ =>
    exteriorFormSpace.smul_mem _ (exteriorBasisForm_mem i))

/-- The restriction uses the shared certified basis, not an independent model. -/
theorem testForm_upper (t : Fin 2) : upperBlockLinear (testForm t) = testRestriction t := by
  obtain ⟨_, hr, hl, hp, hu⟩ := formChecks t
  have hrows : decodeRows (ambientRows t) = decodeExteriorForm (testFormWords.get t) :=
    rectDecode_eq_exterior _ _ hr
  have hleft := packedMul_eq_of_rows _ _ _ hl
  have hproduct := packedMul_eq_of_rows _ _ _ hp
  unfold testForm formCoordinates adaptedBasis
  rw [adapted_transpose, ← hrows, ← decode_packedMul, hleft,
    ← decode_packedMul, hproduct]
  exact hu

theorem testRestriction_mem (t : Fin 2) : testRestriction t ∈ restrictionSpace :=
  ⟨testForm t, testForm_mem t, testForm_upper t⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.ShearRigidity
