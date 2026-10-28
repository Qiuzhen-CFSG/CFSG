module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.ExteriorCoordinates
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Coordinate independence of the exterior and radical families

The first 1221 upper-triangle coordinates of the original exterior family
form the identity matrix. Ten of these coordinates also extract the ten
literal radical coefficients. The finite checks below certify those two
identity blocks, without group-order or invariance assumptions.

Source: `IntrinsicAlgebra/source/README.md` and the reproducible
`Scratch/J4FleetGuidance/SeedCentralizer/explore.py` calculation.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

private theorem independent_of_coordinates {n : ℕ} (f : Fin n → BinaryMatrix)
    (p : Fin n → Fin 112 × Fin 112)
    (h : ∀ i j, f i (p j).1 (p j).2 = if i = j then 1 else 0) :
    LinearIndependent (ZMod 2) f := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hi := congrArg (fun R : BinaryMatrix => R (p i).1 (p i).2) hc
  simpa [Matrix.sum_apply, h] using hi

/-- Independence of precisely the original 1221 exterior forms. -/
theorem exteriorBasisForm_linearIndependent :
    LinearIndependent (ZMod 2) exteriorBasisForm :=
  independent_of_coordinates _ _ exteriorBasisForm_coordinate

theorem finrank_ambientForms : Module.finrank (ZMod 2) ambientForms = 1221 := by
  have hc := finrank_span_eq_card exteriorBasisForm_linearIndependent
  rw [Fintype.card_fin] at hc
  convert! hc using 1

/-- The ten distinguished coordinates in the original exterior family. -/
def radicalCoordinateIndex : Fin 10 → Fin 1221 := ![1210, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220]

set_option maxRecDepth 10000 in
private theorem radicalCoefficient_coordinate : ∀ i j : Fin 10,
    bit (radicalCoefficients.get i) (radicalCoordinateIndex j).val =
      if i = j then 1 else 0 := by
  decide +kernel

theorem ambientRadicalForm_coordinate (i : Fin 10) (j : Fin 1221) :
    ambientRadicalForm i (exteriorCoordinatePair j).1 (exteriorCoordinatePair j).2 =
      bit (radicalCoefficients.get i) j.val := by
  simp [ambientRadicalForm, Matrix.sum_apply, exteriorBasisForm_coordinate]

/-- The literal ten matrices, not just their coefficient words, are independent. -/
theorem ambientRadicalForm_linearIndependent :
    LinearIndependent (ZMod 2) ambientRadicalForm := by
  apply independent_of_coordinates _ (fun j => exteriorCoordinatePair (radicalCoordinateIndex j))
  intro i j
  rw [ambientRadicalForm_coordinate, radicalCoefficient_coordinate]

/-- The span of the exact ten literal forms. Completeness for the radical
condition is a separate assertion. -/
def rawRadicalSpan : Submodule (ZMod 2) BinaryMatrix :=
  Submodule.span (ZMod 2) (Set.range ambientRadicalForm)

theorem finrank_rawRadicalSpan : Module.finrank (ZMod 2) rawRadicalSpan = 10 := by
  have hc := finrank_span_eq_card ambientRadicalForm_linearIndependent
  rw [Fintype.card_fin] at hc
  convert! hc using 1

theorem ambientRadicalForm_mem_ambientForms (i : Fin 10) :
    ambientRadicalForm i ∈ ambientForms := by
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (exteriorBasisForm_mem j)

theorem rawRadicalSpan_le_ambientForms : rawRadicalSpan ≤ ambientForms := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ambientRadicalForm_mem_ambientForms i

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
