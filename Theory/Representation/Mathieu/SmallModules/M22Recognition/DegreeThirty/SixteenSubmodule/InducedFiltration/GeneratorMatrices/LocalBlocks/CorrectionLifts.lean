module
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.Marking
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane.Image.Lifts

/-!
# Explicit matrix lifts of the 44 M22 stabilizer corrections

Each correction, conjugated by the certified explicit M24 marking, is a word
of length at most five in the certified pointwise-pair transvections. Finite
permutation certificates establish the literal embedding identity. Products of
the corresponding determinant-one matrices over `PairPlaneCoordinates.Four`
then identify its image under the existing `PairPlane.pointwiseEquiv`, using
the adjusted coordinates and the original field equivalence.

The finite checks first replace the native generator words and marking by
proved lookup tables. This avoids repeating their expensive reductions for
every correction. Word discovery is reproducible with the adjacent
`CorrectionLifts/source/generate.py`; only the Lean kernel certificates are
used in the proofs. Determinants and projective images are proved structurally.

Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457. This is the local
matrix calculation for the induced module, not its composition-factor theorem.
The binary-coordinate calculation is connected in `CorrectionLifts.Application`.
-/

open Sporadic.Mathieu MathieuCode
open M23Geometry M23Geometry.PairPlaneCoordinates M23Geometry.PairPlaneImage
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
namespace CorrectionCertificates

private def wordPerm : List (Fin 24) → Equiv.Perm (Fin 23)
  | [] => 1
  | t :: w => PairPlaneImage.generatorPerm t * wordPerm w

private def extend23 (g : Fin 23 → Fin 23) (p : Fin 24) : Fin 24 :=
  if p = 0 then 0 else m23PointEmbedding (g ⟨p.val % 23, Nat.mod_lt _ (by decide)⟩)

private def extend22 (g : Fin 22 → Fin 22) (p : Fin 24) : Fin 24 :=
  if p = 0 ∨ p = 9 then p else
    m23PointEmbedding (m22M23PointMap
      (g (m22M23PointMapLeftInverse ⟨p.val % 23, Nat.mod_lt _ (by decide)⟩)))

/-- Certified transvection words, in multiplication order, for the 44 corrections. -/
@[expose] public def correctionWord : Fin 2 → Fin 22 → List (Fin 24) :=
  ![
  ![
    [],
    [],
    [10, 1, 15, 19, 2],
    [],
    [],
    [17, 11],
    [],
    [],
    [15, 18, 6, 23, 9],
    [],
    [],
    [],
    [],
    [],
    [],
    [15, 10],
    [],
    [],
    [7, 19, 10, 7],
    [7, 23, 19, 7],
    [7, 21, 18, 7],
    [3, 13, 11, 3]],
  ![
    [],
    [],
    [],
    [],
    [],
    [22, 3],
    [],
    [],
    [],
    [15, 6, 19, 6],
    [],
    [],
    [],
    [],
    [],
    [],
    [13, 11, 22, 1, 9],
    [],
    [],
    [3, 13, 11, 3],
    [],
    []]]


private def markingPoint : Fin 24 → Fin 24 := ![11, 5, 7, 12, 1, 0, 15, 3, 6, 17, 9, 16, 10, 14, 20, 23, 18, 22, 8, 4, 2, 13, 21, 19]

set_option maxRecDepth 10000 in
private theorem markingPoint_eq : ∀ p, explicitMarkingPerm p = markingPoint p := by
  decide +kernel

private def nativeGeneratorPoint : Fin 2 → Fin 22 → Fin 22 := ![
  ![6, 13, 8, 16, 12, 5, 0, 17, 2, 10, 9, 14, 4, 1, 11, 15, 3, 7, 18, 19, 20, 21],
  ![3, 0, 18, 21, 13, 12, 11, 15, 14, 9, 8, 7, 5, 2, 20, 6, 16, 19, 4, 17, 10, 1]]

private def nativeGeneratorInverse : Fin 2 → Fin 22 → Fin 22 := ![
  ![6, 13, 8, 16, 12, 5, 0, 17, 2, 10, 9, 14, 4, 1, 11, 15, 3, 7, 18, 19, 20, 21],
  ![1, 21, 13, 0, 18, 12, 15, 11, 10, 9, 20, 6, 5, 4, 8, 7, 16, 19, 2, 17, 14, 3]]

private theorem nativeGenerator_left : ∀ k p,
    nativeGeneratorInverse k (nativeGeneratorPoint k p) = p := by decide +kernel

private theorem nativeGenerator_right : ∀ k p,
    nativeGeneratorPoint k (nativeGeneratorInverse k p) = p := by decide +kernel

private def nativeGenerator (k : Fin 2) : Equiv.Perm (Fin 22) where
  toFun := nativeGeneratorPoint k
  invFun := nativeGeneratorInverse k
  left_inv := nativeGenerator_left k
  right_inv := nativeGenerator_right k

private theorem nativeGenerator_eq (k : Fin 2) :
    GeneratorMatrices.generatorPerm k = nativeGenerator k := by
  apply _root_.Equiv.ext
  revert k
  decide +kernel

private def nativeWordPerm : List (Fin 2) → Equiv.Perm (Fin 22)
  | [] => 1
  | k :: w => nativeGenerator k * nativeWordPerm w

private theorem nativeWordPerm_eq (w : List (Fin 2)) :
    GeneratorMatrices.wordPerm w = nativeWordPerm w := by
  induction w with
  | nil => rfl
  | cons k w ih =>
    simp only [GeneratorMatrices.wordPerm, nativeWordPerm, nativeGenerator_eq, ih]

private def nativeCorrection (k : Fin 2) (i : Fin 22) : Equiv.Perm (Fin 22) :=
  nativeWordPerm (GeneratorMatrices.transversalWord i) * nativeGenerator k *
    (nativeWordPerm (GeneratorMatrices.transversalWord ((nativeGenerator k)⁻¹ i)))⁻¹

private theorem nativeCorrection_eq (k : Fin 2) (i : Fin 22) :
    GeneratorMatrices.generatorCorrectionPerm k i = nativeCorrection k i := by
  simp only [GeneratorMatrices.generatorCorrectionPerm, GeneratorMatrices.transversalPerm,
    GeneratorMatrices.generatorPoint, nativeWordPerm_eq, nativeGenerator_eq, nativeCorrection]

set_option maxRecDepth 10000 in
private theorem word_certificate : ∀ (k : Fin 2) (i : Fin 22) (p : Fin 24),
    extend23 (wordPerm (correctionWord k i)) (explicitMarkingPerm p) =
      explicitMarkingPerm (extend22 (GeneratorMatrices.generatorCorrectionPerm k i) p) := by
  simp only [markingPoint_eq, nativeCorrection_eq, extend23, extend22,
    m23PointEmbedding_apply]
  decide +kernel

private noncomputable def wordLift : List (Fin 24) → pointwisePairStabilizer
  | [] => 1
  | t :: w => ⟨generatorLift t, generatorLift_pointwise t⟩ * wordLift w

private theorem wordLift_val (w : List (Fin 24)) : (wordLift w).val.val.val = wordPerm w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    change PairPlaneImage.generatorPerm t * (wordLift w).val.val.val = _
    rw [ih]
    rfl

/-- The existing elementary transvection realized over the executable field. -/
@[expose] public def fourGenerator (t : Fin 24) : Matrix.SpecialLinearGroup (Fin 3) Four :=
  Matrix.SpecialLinearGroup.transvection (generator_ne t) (generatorCoeff t)

/-- Multiply determinant-one transvections with the rightmost factor acting first. -/
@[expose] public def wordMatrix : List (Fin 24) → Matrix.SpecialLinearGroup (Fin 3) Four
  | [] => 1
  | t :: w => fourGenerator t * wordMatrix w

private theorem fourGenerator_map (t : Fin 24) :
    Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom (fourGenerator t) = generatorMatrix t := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change fieldEquiv ((Matrix.transvection (generatorFirst t) (generatorSecond t)
    (generatorCoeff t)) i j) =
      (Matrix.transvection (generatorFirst t) (generatorSecond t) (fieldEquiv (generatorCoeff t))) i j
  simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply, apply_ite fieldEquiv]

private theorem generator_pointwiseEquiv (t : Fin 24) :
    PairPlane.pointwiseEquiv ⟨generatorLift t, generatorLift_pointwise t⟩ =
      (generatorMatrix t : Matrix.PSL3Four.PSL) := by
  apply Matrix.PSL3Four.pslCollineation_injective
  rw [PairPlane.pointwiseEquiv_collineation]
  exact generatorLift_collineation t

private theorem wordLift_pointwiseEquiv (w : List (Fin 24)) :
    PairPlane.pointwiseEquiv (wordLift w) =
      ((Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom (wordMatrix w) : Matrix.PSL3Four.SL) :
        Matrix.PSL3Four.PSL) := by
  induction w with
  | nil => simp [wordLift, wordMatrix]
  | cons t w ih =>
    simp only [wordLift, wordMatrix, map_mul, generator_pointwiseEquiv, ih, fourGenerator_map]
    rfl

private theorem pointEmbedding_extend23 (g : M23) (p : Fin 24) :
    (pointEmbedding g).val p = extend23 g.val p := by
  by_cases hp : p = 0
  · subst p
    exact pointEmbedding_fixed g
  · have he : m23PointEmbedding ⟨p.val % 23, Nat.mod_lt _ (by decide)⟩ = p := by
      revert p
      decide +kernel
    rw [extend23, if_neg hp, ← pointEmbedding_apply, he]

private theorem m22Embedding_extend22 (g : M22) (p : Fin 24) :
    (m22Embedding g).val p = extend22 g.val p := by
  by_cases hp : p = 0 ∨ p = 9
  · rcases hp with rfl | rfl
    · exact m22Embedding_fixed_zero g
    · exact m22Embedding_fixed_nine g
  · have he : m22Coordinates (m22M23PointMapLeftInverse
        ⟨p.val % 23, Nat.mod_lt _ (by decide)⟩) = p := by
      revert p
      decide +kernel
    rw [extend22, if_neg hp]
    have h := m22Embedding_apply g
      (m22M23PointMapLeftInverse ⟨p.val % 23, Nat.mod_lt _ (by decide)⟩)
    rw [he] at h
    exact h

private theorem pairEmbedding_wordLift (w : List (Fin 24)) (p : Fin 24) :
    (pairEmbedding (wordLift w)).val p = extend23 (wordPerm w) p := by
  change (pointEmbedding (wordLift w).val.val).val p = _
  rw [pointEmbedding_extend23, wordLift_val]

private theorem lift_embedding_of_certificate (w : List (Fin 24)) (k : Fin 2) (i : Fin 22)
    (h : ∀ p : Fin 24, extend23 (wordPerm w) (explicitMarkingPerm p) =
      explicitMarkingPerm (extend22 (GeneratorMatrices.generatorCorrectionPerm k i) p)) :
    pairEmbedding (wordLift w) = explicitMarking *
      m22Embedding (GeneratorMatrices.generatorCorrection k i).val * explicitMarking⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro p
  change (pairEmbedding (wordLift w)).val (explicitMarking.val p) =
    explicitMarking.val ((m22Embedding (GeneratorMatrices.generatorCorrection k i).val).val p)
  rw [explicitMarking_val, pairEmbedding_wordLift, m22Embedding_extend22,
    GeneratorMatrices.generatorCorrection_val]
  exact h p

end CorrectionCertificates
/-- The explicit pair-subgroup lift of each native M22 stabilizer correction. -/
public noncomputable def correctionLift (k : Fin 2) (i : Fin 22) :
    M23Geometry.pointwisePairStabilizer :=
  CorrectionCertificates.wordLift (CorrectionCertificates.correctionWord k i)

/-- Executable determinant-one matrices in the existing quadratic field of order four.
Their factors are the certified transvections in the adjusted projective coordinates. -/
@[expose] public def correctionMatrix (k : Fin 2) (i : Fin 22) :
    Matrix.SpecialLinearGroup (Fin 3) M23Geometry.PairPlaneCoordinates.Four :=
  CorrectionCertificates.wordMatrix (CorrectionCertificates.correctionWord k i)

/-- The lifts are the literal conjugates of the native stabilizer corrections. -/
public theorem correctionLift_embedding (k : Fin 2) (i : Fin 22) :
    pairEmbedding (correctionLift k i) = explicitMarking *
      MathieuCode.m22Embedding (GeneratorMatrices.generatorCorrection k i).val *
        explicitMarking⁻¹ :=
  CorrectionCertificates.lift_embedding_of_certificate _ k i
    (CorrectionCertificates.word_certificate k i)

/-- Identification in the existing adjusted projective marking, with the literal field map. -/
public theorem correctionLift_pointwiseEquiv (k : Fin 2) (i : Fin 22) :
    M23Geometry.PairPlane.pointwiseEquiv (correctionLift k i) =
      ((Matrix.SpecialLinearGroup.map M23Geometry.PairPlaneCoordinates.fieldEquiv.toRingHom
        (correctionMatrix k i) : Matrix.PSL3Four.SL) : Matrix.PSL3Four.PSL) :=
  CorrectionCertificates.wordLift_pointwiseEquiv _

/-- These executable matrices intertwine all 44 native corrections under one coordinate change. -/
public theorem correctionMatrix_intertwines (k : Fin 2) (i : Fin 22) (v : Adjoint) :
    markingChange (pointAdjoint (GeneratorMatrices.generatorCorrection k i) v) =
      adjointBinary (Matrix.SpecialLinearGroup.map
        M23Geometry.PairPlaneCoordinates.fieldEquiv.toRingHom (correctionMatrix k i))
        (markingChange v) := by
  rw [markingChange_intertwines _ _ (correctionLift_embedding k i),
    correctionLift_pointwiseEquiv, projectiveAdjoint_mk]

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
