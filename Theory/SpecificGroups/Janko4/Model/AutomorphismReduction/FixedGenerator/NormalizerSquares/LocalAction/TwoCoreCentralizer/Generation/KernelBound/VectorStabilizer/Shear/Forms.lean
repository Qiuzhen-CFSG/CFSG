module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Shear.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.FiniteRestriction.QuadraticRelations.LinearMembership.RadicalCertificate.Arithmetic

/-!
# The two selected exterior forms and their shear-test blocks

Each selected form is certified as the displayed linear combination of the
original exterior generators. Its ambient rows satisfy Eᵀ R = testIU Q,
where Q is the lift projection from the actual inverse adapted basis.
The already checked identities Q E = Q H = 0 and Q L = 1 give all three
required blocks. This uses no dimension, radical bound, or group-generation
hypothesis.

The numerical certificates use ordinary kernel reduction. Their witnesses
are reproduced by VectorStabilizer/source/explore.py and
Shear/source/generate_data.py; see ../source/README.md and source/README.md
for the matrix provenance and bit conventions.
-/

public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates RadicalCertificate

private def ambientRows : Vector (Vector ℕ 112) 2 :=
  ⟨#[testAmbientRows0, testAmbientRows1], rfl⟩

private def projectionRows : Vector ℕ 50 :=
  Vector.ofFn (fun i => adaptedInverseRows.get (liftIndex i))

private theorem projection_decode :
    liftProjection = rectDecode 112 projectionRows := by
  ext i j
  simp only [liftProjection, adaptedInverse, projectionRows, rectDecode,
    Matrix.submatrix_apply, id_eq, get_ofFn]

private def FormChecks (t : Fin 2) : Prop :=
  scan (testCoefficients.get t) exteriorFormRows.toList = testFormWords.get t ∧
  (∀ i j : Fin 112, ((ambientRows.get t).get i).testBit j.val =
    if i < j then (testFormWords.get t).testBit (exteriorIndex i j)
    else if j < i then (testFormWords.get t).testBit (exteriorIndex j i) else false) ∧
  (∀ i : Fin 50,
    scan (restrictionColumns.get i) (ambientRows.get t).toList =
    scan ((testIURows.get t).get i) projectionRows.toList)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked0 : FormChecks 0 := by
  simp only [FormChecks, projectionRows, Vector.toList_ofFn]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem checked1 : FormChecks 1 := by
  simp only [FormChecks, projectionRows, Vector.toList_ofFn]
  decide +kernel

private theorem all_checks (t : Fin 2) : FormChecks t := by
  fin_cases t
  · exact checked0
  · exact checked1

attribute [local irreducible] testCoefficients testFormWords ambientRows projectionRows
  exteriorFormRows testIURows exteriorFormSpace

private theorem product_eq_product {m n k l : ℕ}
    (xs : Vector ℕ m) (ys : Vector ℕ n) (zs : Vector ℕ m) (ws : Vector ℕ l)
    (h : ∀ i, scan (xs.get i) ys.toList = scan (zs.get i) ws.toList) :
    rectDecode n xs * rectDecode k ys = rectDecode l zs * rectDecode k ws := by
  rw [← rectDecode_product, ← rectDecode_product]
  congr 1
  apply Vector.ext
  intro i hi
  change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
  simpa only [get_ofFn, ← scan_eq] using h ⟨i, hi⟩

private theorem testForm_factorization (t : Fin 2) :
    testForm t ∈ exteriorFormSpace ∧
      restrictionEmbeddingᵀ * testForm t = testIU t * liftProjection := by
  obtain ⟨hc, hr, hp⟩ := all_checks t
  have hext : testForm t ∈ exteriorFormSpace := by
    rw [testForm, ← hc, scan_eq, decodeExteriorForm_combination]
    exact exteriorFormSpace.sum_mem (fun j _ =>
      exteriorFormSpace.smul_mem _ (exteriorBasisForm_mem j))
  have hrows : rectDecode 112 (ambientRows.get t) = testForm t :=
    rectDecode_eq_exterior _ _ hr
  refine ⟨hext, ?_⟩
  rw [← hrows, projection_decode]
  change rectDecode 112 restrictionColumns * rectDecode 112 (ambientRows.get t) =
    rectDecode 50 (testIURows.get t) * rectDecode 112 projectionRows
  exact product_eq_product _ _ _ _ hp

/-- Both selected forms belong to the actual exterior span and have the
required blocks for the published E, H and L embeddings. -/
theorem testForm_spec (t : Fin 2) :
    testForm t ∈ exteriorFormSpace ∧
      restrictionEmbeddingᵀ * testForm t * restrictionEmbedding = 0 ∧
      restrictionEmbeddingᵀ * testForm t * mixedEmbedding = 0 ∧
      restrictionEmbeddingᵀ * testForm t * restrictionLifts = testIU t := by
  obtain ⟨hext, hf⟩ := testForm_factorization t
  refine ⟨hext, ?_, ?_, ?_⟩
  · rw [hf, Matrix.mul_assoc, liftProjection_embedding, Matrix.mul_zero]
  · rw [hf, Matrix.mul_assoc, liftProjection_mixed, Matrix.mul_zero]
  · rw [hf, Matrix.mul_assoc, liftProjection_lifts, Matrix.mul_one]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Shear
