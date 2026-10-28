module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Independence

/-!
# Unique coordinates in the original exterior family

The certified identity block extracts every exterior coefficient by a matrix
entry. Thus completeness of the radical calculation can be checked as a
1211-equation elimination in this exact coefficient space. The final lemma
turns those coefficient equations into membership in the ten-form span.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Read one of the original exterior coordinates directly from a matrix. -/
def ambientCoefficient (R : BinaryMatrix) (j : Fin 1221) : ZMod 2 :=
  R (exteriorCoordinatePair j).1 (exteriorCoordinatePair j).2

theorem ambientCoefficient_sum (c : Fin 1221 → ZMod 2) (j : Fin 1221) :
    ambientCoefficient (∑ k, c k • exteriorBasisForm k) j = c j := by
  simp [ambientCoefficient, Matrix.sum_apply, exteriorBasisForm_coordinate]

/-- Every ambient form is recovered from its actual matrix entries. -/
theorem ambientForm_reconstruction {R : BinaryMatrix} (hR : R ∈ ambientForms) :
    ∑ j : Fin 1221, ambientCoefficient R j • exteriorBasisForm j = R := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hR
  simp only [ambientCoefficient_sum]

theorem ambientForm_ext {R S : BinaryMatrix} (hR : R ∈ ambientForms)
    (hS : S ∈ ambientForms) (h : ∀ j, ambientCoefficient R j = ambientCoefficient S j) :
    R = S := by
  rw [← ambientForm_reconstruction hR, ← ambientForm_reconstruction hS]
  simp only [h]

/-- Once the radical coefficient equations are certified, they reconstruct
membership in the exact ten-form span. No completeness assertion is assumed
about a different family of forms. -/
theorem mem_rawRadicalSpan_of_coordinates {R : BinaryMatrix} (hR : R ∈ ambientForms)
    (hc : ∀ j : Fin 1221, ambientCoefficient R j =
      ∑ i : Fin 10, ambientCoefficient R (radicalCoordinateIndex i) *
        bit (radicalCoefficients.get i) j.val) : R ∈ rawRadicalSpan := by
  let S := ∑ i : Fin 10, ambientCoefficient R (radicalCoordinateIndex i) • ambientRadicalForm i
  have hS : S ∈ rawRadicalSpan := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have he : R = S := by
    apply ambientForm_ext hR (rawRadicalSpan_le_ambientForms hS)
    intro j
    rw [hc j]
    simp only [S, ambientCoefficient, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, ambientRadicalForm_coordinate]
  exact he.symm ▸ hS

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
