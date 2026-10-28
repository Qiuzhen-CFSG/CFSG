module

public import Theory.SpecificGroups.Triality.BinarySevenPlane.Curves
public import Theory.SpecificGroups.Triality.BinarySevenPlane.Certificate.Witness

/-!
# An explicit Lang witness in the genuine binary triality split group

The eleven canonical root factors lie in the actual extension field. Their
faithful full-lattice matrix images specialize the checked cubic-ring
certificate. The six root curves are graph-fixed, so graph-field squares their
parameters; the certificate proves sigma(x) = x*n_w with the specified Weyl
word and orientation. No general Lang theorem or alternative group model is
used. Source: the explicit nonsplit seven-torus construction at q = 2,
motivated by ATLAS, printed p.89.
-/

@[expose] public section
namespace Triality.Standard.BinarySevenPlane
open ConcreteBruhat ConcreteBruhat.MatrixRealization
open PositiveCoordinates.SumExchangeData Coefficients
noncomputable section
local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "F" => ExtensionField P

def matrix28 : SplitGroup P →* Matrix (Fin 28) (Fin 28) F :=
  (Matrix.reindexRingEquiv F finSumFinEquiv).toMonoidHom.comp (matrix P)

lemma matrix28_injective : Function.Injective matrix28 :=
  (Matrix.reindexRingEquiv F finSumFinEquiv).injective.comp (matrix_injective P)

lemma matrix28_root (r) (t : Scalar) : matrix28 (root r (actualMap t)) =
    actualMap.mapMatrix (Certificate.curve r t) := by
  change Matrix.reindexRingEquiv F finSumFinEquiv (matrix P (root r (actualMap t))) = _
  rw [matrix_root, ← map_matrixCurve actualMap]
  ext i j
  simp only [Certificate.curve, Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply]

lemma matrix_wordCoefficient (l) : matrix P (word l) =
    actualMap.mapMatrix (Certificate.wordCoefficient l) := by
  ext a b
  rw [(realizes_word l).matrix_column]
  simp only [rootAction_rootWord, RingHom.mapMatrix_apply, Matrix.map_apply,
    Certificate.wordCoefficient]
  cases b with
  | inl j => cases a <;> simp [corootVector]
  | inr r => dsimp only; split_ifs <;> simp

lemma matrix28_twistWord : matrix28 twistWord = actualMap.mapMatrix Certificate.weylMatrix := by
  change Matrix.reindexRingEquiv F finSumFinEquiv (matrix P (word [1,0,2,3,1,0,2,3])) = _
  rw [matrix_wordCoefficient, Certificate.weylMatrix_eq]
  ext i j
  simp only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply]

/-- The eleven specified canonical root factors, in the literal extension field. -/
def langWitness : SplitGroup P :=
  root 14 (actualMap ⟨2⟩) * root 3 (actualMap ⟨4⟩) *
  root 4 (actualMap ⟨1⟩) * root 7 (actualMap ⟨1⟩) *
  root 4 (actualMap ⟨2⟩) * root 7 (actualMap ⟨6⟩) *
  root 4 (actualMap ⟨3⟩) * root 13 (actualMap ⟨1⟩) *
  root 7 (actualMap ⟨7⟩) * root 0 (actualMap ⟨6⟩) * root 4 (actualMap ⟨7⟩)

lemma matrix28_langWitness : matrix28 langWitness = actualMap.mapMatrix Certificate.curveWord := by
  simp only [langWitness, Certificate.curveWord, map_mul, matrix28_root]

lemma matrix28_graphField_langWitness : matrix28 (graphFieldAutomorphism P langWitness) =
    actualMap.mapMatrix ((frobenius Scalar 2).mapMatrix Certificate.curveWord) := by
  have hf (r) (t : Scalar) : (frobenius Scalar 2).mapMatrix (Certificate.curve r t) =
      Certificate.curve r (t^2) := by
    unfold Certificate.curve
    ext i j
    have he := map_matrixCurve (frobenius Scalar 2) r t
    have hh := congrFun (congrFun he (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
    simpa only [Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, frobenius_def] using hh
  simp only [langWitness, map_mul, graphField_root14, graphField_root3,
    graphField_root4, graphField_root7, graphField_root13, graphField_root0,
    ← map_pow, matrix28_root, Certificate.curveWord, hf]

/-- Exact Lang identity in the original Geck group; no general Lang theorem is used. -/
theorem graphField_langWitness : graphFieldAutomorphism P langWitness = langWitness * twistWord := by
  apply matrix28_injective
  rw [matrix28_graphField_langWitness, Certificate.frobenius_curveWord,
    map_mul, map_mul, matrix28_langWitness, matrix28_twistWord]

end
end Triality.Standard.BinarySevenPlane
