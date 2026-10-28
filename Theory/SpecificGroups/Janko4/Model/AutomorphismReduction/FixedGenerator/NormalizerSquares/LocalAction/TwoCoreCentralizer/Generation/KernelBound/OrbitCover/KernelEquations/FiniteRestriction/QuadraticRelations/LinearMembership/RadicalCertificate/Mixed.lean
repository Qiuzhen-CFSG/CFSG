module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.CheckedForms

/-!
# The mixed image of the displayed radical span

Explicit binary change-of-generator coefficients give both inclusions between
the image of the 53 displayed forms and the forty-generator mixed space.
Linearity extends the row factorization from those forms to their span.
The separate completeness certificate must identify this span with the actual
exterior radical. See ../../source/README.md for the source and conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
open GeneratorCertificates

private theorem combination_eq {m n t : ℕ} (xs : Vector (Vector ℕ m) t)
    (c : ℕ) (ys : Vector ℕ m)
    (h : ∀ i, scan c (List.ofFn (fun j => (xs.get j).get i)) = ys.get i) :
    rectDecode n ys = ∑ j : Fin t, bit c j.val • rectDecode n (xs.get j) := by
  rw [← rectDecode_combination]
  congr 1
  apply Vector.ext
  intro i hi
  change ys.get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  rw [get_ofFn]
  symm
  simpa only [scan_ofFn, rectRowProduct, get_ofFn] using h ⟨i, hi⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem image_checks : ∀ i : Fin 53, ∀ j : Fin 12,
    scan (imageCoefficients.get i)
      (List.ofFn (fun k : Fin 40 => (mixedGeneratorRows.get k).get j)) =
    (radicalMixedRows.get i).get j := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem generator_checks : ∀ i : Fin 40, ∀ j : Fin 12,
    scan (generatorCoefficients.get i)
      (List.ofFn (fun k : Fin 53 => (radicalMixedRows.get k).get j)) =
    (mixedGeneratorRows.get i).get j := by
  decide +kernel

private theorem image_in_mixedSpace (i : Fin 53) :
    mixedEvaluation (radicalGenerator i) ∈ mixedSpace := by
  rw [radicalGenerator_mixed,
    combination_eq mixedGeneratorRows _ _ (image_checks i)]
  apply mixedSpace.sum_mem
  intro j _
  exact mixedSpace.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem generator_in_image (i : Fin 40) :
    mixedGenerator i ∈ radicalSpan.map mixedEvaluation := by
  change rectDecode 50 (mixedGeneratorRows.get i) ∈ _
  rw [combination_eq radicalMixedRows _ _ (generator_checks i)]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  rw [← radicalGenerator_mixed]
  exact ⟨radicalGenerator j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

/-- Both inclusions are checked; no completeness assertion is used. -/
theorem radicalSpan_mixed_image : radicalSpan.map mixedEvaluation = mixedSpace := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact image_in_mixedSpace i
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact generator_in_image i

/-- The displayed forms satisfy the requested factorization, hence so does
any linear combination of them. -/
theorem radicalSpan_factorization (R : BinaryMatrix) (hR : R ∈ radicalSpan) :
    mixedEmbeddingᵀ * R =
      mixedEvaluation R * restrictionExtraction * (matrixA - 1) := by
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨i, rfl⟩ := hR
    exact radicalGenerator_factorization i
  | zero => simp only [Matrix.mul_zero, map_zero, Matrix.zero_mul]
  | add R S hR hS ihR ihS =>
    simp only [Matrix.mul_add, map_add, Matrix.add_mul, ihR, ihS]
  | smul c R hR ihR =>
    simp only [Matrix.mul_smul, map_smul, Matrix.smul_mul, ihR]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.LinearMembership.RadicalCertificate
