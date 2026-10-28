module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.ExteriorAnnihilators.Data

/-!
# Calibration and transport of the exterior functionals

The embedding rows are checked against the published columns. Moving the
restriction across the matrix pairing then reduces annihilation to a binary
dot product with each original full exterior form. Source: source/README.md.
-/

@[expose] public section
open scoped Matrix
open Janko4.GeneratorCertificates
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators
open PullbackCoefficients ExteriorInvariance

set_option maxRecDepth 10000 in
theorem embeddingRows_eq : embeddingRows = rowsTranspose 112 restrictionColumns := by
  have h : ∀ i : Fin 112, embeddingRows.get i =
      xorList (List.ofFn (fun j : Fin 50 =>
        if (restrictionColumns.get j).testBit i.val then 2^j.val else 0)) := by decide +kernel
  apply Vector.ext
  intro i hi
  change embeddingRows.get ⟨i, hi⟩ = (rowsTranspose 112 restrictionColumns).get ⟨i, hi⟩
  rw [rowsTranspose, get_ofFn]
  exact h ⟨i, hi⟩

theorem embeddingRows_spec : rowsMatrix (n := 50) embeddingRows = restrictionEmbedding := by
  rw [embeddingRows_eq, rowsMatrix_transpose]
  rfl

theorem restrictionColumns_spec :
    rowsMatrix (n := 112) restrictionColumns = restrictionEmbeddingᵀ := rfl

set_option maxRecDepth 10000 in
theorem testIndex_spec : ∀ e : Fin 987, (tests.get e).1.val ≠ 0 →
    (tests.get e).2 = weights.get (testIndex.get e) := by
  decide +kernel

def transportRow (w : ℕ) (i : Fin 112) : ℕ :=
  rowProduct (xorList (List.ofFn (fun k : Fin 50 =>
    if (embeddingRows.get i).testBit k.val then weightRow w k else 0))) restrictionColumns

attribute [local irreducible] restrictionColumns embeddingRows weightRows restrictionEmbedding

theorem transportRow_eq (w : ℕ) (i : Fin 112) :
    transportRow w i =
      rowProduct (rowProduct (embeddingRows.get i) (weightRows w)) restrictionColumns := by
  simp only [transportRow, rowProduct, weightRows, get_ofFn]

theorem flat_transport (w d : ℕ)
    (h : ∀ i : Fin 112, transportRow w i = flatRow d i.val) :
    flatMatrix d = restrictionEmbedding * rowsMatrix (weightRows w) * restrictionEmbeddingᵀ := by
  have he : rowsMatrix (n := 112)
      (rowsProduct (rowsProduct embeddingRows (weightRows w)) restrictionColumns) = flatMatrix d := by
    funext i j
    simp only [rowsMatrix, rowsProduct, get_ofFn]
    rw [← transportRow_eq, h, flatRow_bit]
  rw [rowsMatrix_product, rowsMatrix_product, embeddingRows_spec, restrictionColumns_spec] at he
  exact he.symm

theorem upperValue_zero_of_flat (w d r : ℕ)
    (htransport : ∀ i : Fin 112, transportRow w i = flatRow d i.val)
    (hdot : flatDot d r = false) :
    upperValue w (restrictionForm (flatMatrix r)) = 0 := by
  rw [← transport_spec, ← flat_transport w d htransport, ← flatDot_spec, hdot]
  rfl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.ExteriorAnnihilators
