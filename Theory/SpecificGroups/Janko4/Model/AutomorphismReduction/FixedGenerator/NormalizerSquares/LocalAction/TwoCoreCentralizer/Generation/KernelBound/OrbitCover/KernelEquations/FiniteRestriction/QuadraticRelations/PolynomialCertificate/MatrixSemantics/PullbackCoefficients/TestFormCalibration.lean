module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.TestFormData
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.PolynomialCertificate.MatrixSemantics.PullbackCoefficients.Arithmetic
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.BasisBlock0000

/-!
# Calibration of the packed restriction test forms

The nine candidate row arrays are exactly the restrictions of the original
112-dimensional exterior forms to the published displacement columns. We
recover full rows from the certified ambient encodings, interpret packed
multiplication and transpose as matrix operations, and check the resulting
nine arrays by kernel reduction. Block zero is the published restriction
pairing, so its calibration is definitional.

Source and ATLAS attribution: the polynomial certificate's `source/README.md`,
`QuadraticRelations.RestrictionData`, and `Janko4/Model/Data.lean`. The candidate
arrays and their discovery provenance are recorded in `TestFormData`; their
identification here assumes no group or polynomial coefficient hypothesis.
-/

@[expose] public section
open scoped Matrix

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients
open GeneratorCertificates ExteriorInvariance

private def ambientRows (i : Fin 9) : Vector ℕ 112 :=
  Vector.ofFn (fun r => flatRow (basisFlat i.val) r.val)

private theorem ambientRows_spec (i : Fin 9) :
    rowsMatrix (n := 112) (ambientRows i) = exteriorBasisForm ⟨i.val, by omega⟩ := by
  rw [← basis_decodeBlock0000 i.val (Nat.zero_le _) (by omega) (by omega)]
  funext r c
  change bit ((Vector.ofFn (fun r : Fin 112 => flatRow (basisFlat i.val) r.val)).get r) c.val = _
  rw [get_ofFn]
  exact flatRow_bit _ _ _

private theorem columns_spec :
    rowsMatrix (n := 112) restrictionColumns = restrictionEmbeddingᵀ := by
  rfl

private def computedRows (i : Fin 9) : Vector ℕ 50 :=
  rowsProduct (rowsProduct restrictionColumns (ambientRows i))
    (rowsTranspose 112 restrictionColumns)

private theorem computedRows_spec (i : Fin 9) :
    rowsMatrix (n := 50) (computedRows i) = restrictionTestForm i := by
  rw [computedRows, rowsMatrix_product, rowsMatrix_product, rowsMatrix_transpose,
    ambientRows_spec, columns_spec, Matrix.transpose_transpose]
  rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem computedRows_lists : ∀ i : Fin 9,
    (computedRows i).toList = (exteriorTestRows.get i).toList := by
  simp only [computedRows, rowsProduct, Vector.toList_ofFn, rowProduct,
    ambientRows, rowsTranspose, get_ofFn]
  decide +kernel

private theorem computedRows_eq (i : Fin 9) : computedRows i = exteriorTestRows.get i :=
  Vector.toList_inj.mp (computedRows_lists i)

/-- The candidate exterior rows decode to the actual restricted ambient forms. -/
theorem exteriorTestRows_spec (i : Fin 9) :
    decodeRestrictionRows (exteriorTestRows.get i) = restrictionTestForm i := by
  rw [← computedRows_eq i]
  exact computedRows_spec i

/-- Every packed test form decodes to its actual matrix, without extra premises. -/
theorem testFormRows_spec (b : Fin 10) :
    decodeRestrictionRows (testFormRows b) = testForm b := by
  by_cases hb : b.val = 0
  · simp only [testFormRows, testForm, hb, ↓reduceDIte]
    rfl
  · simp only [testFormRows, testForm, hb, ↓reduceDIte]
    exact exteriorTestRows_spec _

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates.PolynomialCertificate.PullbackCoefficients
