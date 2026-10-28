module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.GeneratorMatrices.LocalBlocks.Marking

/-!
# Explicit binary coordinates for the F₄ adjoint

The actual trace-kernel representation has eight field coordinates, in the
order `(01, 02, 10, 12, 20, 21, 00, 11)`. Transport through the existing
`PairPlaneCoordinates.fieldEquiv` identifies these entries with the quadratic
algebra F₂[a], where a² = a + 1. The first eight binary coordinates are the
constant coefficients; the last eight are the coefficients of a.

The inverse inserts these entries into a matrix and fills the last diagonal
entry with the negative sum of the first two. The matrix of conjugation is
computed column by column using these explicit vectors and the adjugate.
Thus `binaryMatrix` is executable without choosing a basis or computing an
inverse in the noncomputable canonical field. Its comparison with the actual
adjoint action follows by transporting matrix multiplication and adjugation.

The trace-coordinate pattern follows
`Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates`.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457. This is a coordinate
construction for the local model, not the sporadic recognition theorem.
-/

public section

open Matrix Representation Sporadic.Mathieu.M23Geometry.PairPlaneCoordinates
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks

private def matrixOfEight {R : Type*} [CommRing R] (v : Fin 8 → R) :
    Matrix (Fin 3) (Fin 3) R :=
  !![v 6, v 0, v 1; v 2, v 7, v 3; v 4, v 5, -(v 6 + v 7)]

private def readEight {R : Type*} (X : Matrix (Fin 3) (Fin 3) R) : Fin 8 → R :=
  ![X 0 1, X 0 2, X 1 0, X 1 2, X 2 0, X 2 1, X 0 0, X 1 1]

private theorem matrixOfEight_trace {R : Type*} [CommRing R] (v : Fin 8 → R) :
    (matrixOfEight v).trace = 0 := by
  simp [matrixOfEight, Matrix.trace, Fin.sum_univ_three]

private theorem matrixOfEight_read {R : Type*} [CommRing R]
    (X : Matrix (Fin 3) (Fin 3) R) (hX : X.trace = 0) :
    matrixOfEight (readEight X) = X := by
  have hd : -(X 0 0 + X 1 1) = X 2 2 := by
    have h : X 0 0 + X 1 1 + X 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using hX
    exact (neg_eq_iff_add_eq_zero).mpr h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOfEight, readEight, hd]

private noncomputable def eightCoordinates : Adjoint ≃ₗ[Matrix.PSL3Four.F]
    (Fin 8 → Matrix.PSL3Four.F) where
  toFun v := readEight (LinearMap.toMatrix' v.val)
  invFun v := ⟨(matrixOfEight v).toLin', by
    change (LinearMap.trace _ _) (matrixOfEight v).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact matrixOfEight_trace v⟩
  left_inv v := by
    apply Subtype.ext
    change (matrixOfEight (readEight (LinearMap.toMatrix' v.val))).toLin' = v.val
    rw [matrixOfEight_read, Matrix.toLin'_toMatrix']
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
    exact v.property
  right_inv v := by
    change readEight (LinearMap.toMatrix' (matrixOfEight v).toLin') = v
    rw [LinearMap.toMatrix'_toLin']
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    change readEight (LinearMap.toMatrix' (v.val + w.val)) = _
    rw [map_add]
    funext i
    fin_cases i <;> rfl
  map_smul' c v := by
    change readEight (LinearMap.toMatrix' (c • v.val)) = _
    rw [map_smul]
    funext i
    fin_cases i <;> rfl

/-- The existing field identification, read backwards as a binary linear equivalence. -/
noncomputable def coefficientEquiv : Matrix.PSL3Four.F ≃ₗ[ZMod 2] Four :=
  fieldEquiv.symm.toAddEquiv.toLinearEquiv (ZMod.map_smul _)

private noncomputable def eightCoefficientEquiv :
    (Fin 8 → Matrix.PSL3Four.F) ≃ₗ[ZMod 2] (Fin 8 → Four) where
  toFun v i := coefficientEquiv (v i)
  invFun v i := coefficientEquiv.symm (v i)
  left_inv v := by funext i; exact coefficientEquiv.symm_apply_apply _
  right_inv v := by funext i; exact coefficientEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact coefficientEquiv.map_add _ _
  map_smul' c v := by funext i; exact coefficientEquiv.map_smul c _

/-- Reassemble eight quadratic entries from the constant and quadratic coefficient halves. -/
@[expose] def unpackBinary (v : Fin 16 → ZMod 2) : Fin 8 → Four :=
  fun i => ⟨v (Fin.castAdd 8 i), v (Fin.natAdd 8 i)⟩

/-- Read constant coefficients first and quadratic coefficients second. -/
@[expose] def packBinary (v : Fin 8 → Four) : Fin 16 → ZMod 2 :=
  Fin.append (fun i => (v i).re) (fun i => (v i).im)

private def splitCoefficients : (Fin 8 → Four) ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) where
  toFun := packBinary
  invFun := unpackBinary
  left_inv v := by
    funext i
    simp only [unpackBinary, packBinary, Fin.append_left, Fin.append_right]
  right_inv v := by
    funext i
    fin_cases i <;> rfl
  map_add' v w := by
    funext i
    fin_cases i <;> rfl
  map_smul' c v := by
    funext i
    fin_cases i <;> rfl

/-- Explicit binary coordinates on the literal trace-kernel representation. -/
noncomputable def binaryCoordinates : Adjoint ≃ₗ[ZMod 2] (Fin 16 → ZMod 2) :=
  ((eightCoordinates.restrictScalars (ZMod 2)).trans eightCoefficientEquiv).trans
    splitCoefficients

/-- The trace-zero quadratic matrix represented by a binary coordinate vector. -/
@[expose] def binaryMatrixOf (v : Fin 16 → ZMod 2) : Matrix (Fin 3) (Fin 3) Four :=
  let w := unpackBinary v
  !![w 6, w 0, w 1; w 2, w 7, w 3; w 4, w 5, -(w 6 + w 7)]

/-- Read the sixteen selected binary coefficients of a quadratic matrix. -/
@[expose] def binaryReadMatrix (X : Matrix (Fin 3) (Fin 3) Four) : Fin 16 → ZMod 2 :=
  packBinary ![X 0 1, X 0 2, X 1 0, X 1 2, X 2 0, X 2 1, X 0 0, X 1 1]

/-- Executable conjugation matrix: column `j` is the image of the explicit `j`th vector. -/
@[expose] def binaryMatrix (A : Matrix.SpecialLinearGroup (Fin 3) Four) :
    Matrix (Fin 16) (Fin 16) (ZMod 2) :=
  fun i j => binaryReadMatrix (A.val * binaryMatrixOf (Pi.single j 1) *
    Matrix.adjugate A.val) i

/-- The coordinates read the actual endomorphism matrix through the fixed field transport. -/
theorem binaryCoordinates_apply (v : Adjoint) :
    binaryCoordinates v =
      binaryReadMatrix ((LinearMap.toMatrix' v.val).map fieldEquiv.symm) := by
  funext i
  fin_cases i <;> rfl

/-- Reconstructing a coordinate vector gives its explicit matrix in the canonical field. -/
theorem binaryCoordinates_symm_matrix (v : Fin 16 → ZMod 2) :
    LinearMap.toMatrix' (binaryCoordinates.symm v).val =
      (binaryMatrixOf v).map fieldEquiv := by
  change LinearMap.toMatrix' (matrixOfEight
    (fun i => fieldEquiv (unpackBinary v i))).toLin' = _
  rw [LinearMap.toMatrix'_toLin']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfEight, binaryMatrixOf, Matrix.map_apply]

private theorem adjointBinary_matrix (g : Matrix.PSL3Four.SL) (v : Adjoint) :
    LinearMap.toMatrix' (adjointBinary g v).val =
      g.val * LinearMap.toMatrix' v.val * (g⁻¹).val := by
  change LinearMap.toMatrix' ((g.val.toLin' ∘ₗ v.val) ∘ₗ (g⁻¹).val.toLin') = _
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']

private theorem mapped_adjoint_matrix
    (A : Matrix.SpecialLinearGroup (Fin 3) Four) (v : Adjoint) :
    (LinearMap.toMatrix' (adjointBinary
      (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A) v).val).map fieldEquiv.symm =
      A.val * (LinearMap.toMatrix' v.val).map fieldEquiv.symm * Matrix.adjugate A.val := by
  rw [adjointBinary_matrix, Matrix.SpecialLinearGroup.coe_inv]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  rw [Matrix.map_mul, Matrix.map_mul]
  change (A.val.map fieldEquiv).map fieldEquiv.symm *
    (LinearMap.toMatrix' v.val).map fieldEquiv.symm *
    (Matrix.adjugate (A.val.map fieldEquiv)).map fieldEquiv.symm = _
  have hA : (A.val.map fieldEquiv).map fieldEquiv.symm = A.val := by
    funext i j
    exact fieldEquiv.symm_apply_apply _
  rw [hA]
  have hadj : (Matrix.adjugate (A.val.map fieldEquiv)).map fieldEquiv.symm =
      Matrix.adjugate A.val := by
    change fieldEquiv.symm.toRingHom.mapMatrix _ = _
    rw [RingHom.map_adjugate]
    change Matrix.adjugate ((A.val.map fieldEquiv).map fieldEquiv.symm) = _
    rw [hA]
  rw [hadj]

private theorem binaryMatrix_eq_toMatrix
    (A : Matrix.SpecialLinearGroup (Fin 3) Four) :
    binaryMatrix A = LinearMap.toMatrix' (binaryCoordinates.conj
      (adjointBinary (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A))) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change _ = binaryCoordinates (adjointBinary
    (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A)
    (binaryCoordinates.symm (Pi.single j 1))) i
  rw [binaryCoordinates_apply, mapped_adjoint_matrix, binaryCoordinates_symm_matrix]
  have hX : ((binaryMatrixOf (Pi.single j 1)).map fieldEquiv).map fieldEquiv.symm =
      binaryMatrixOf (Pi.single j 1) := by
    funext a b
    exact fieldEquiv.symm_apply_apply _
  rw [hX]
  rfl

/-- The executable binary matrix is conjugation on the actual adjoint representation. -/
theorem binaryCoordinates_intertwines
    (A : Matrix.SpecialLinearGroup (Fin 3) Four) (v : Adjoint) :
    binaryCoordinates (adjointBinary
      (Matrix.SpecialLinearGroup.map fieldEquiv.toRingHom A) v) =
      (binaryMatrix A).mulVec (binaryCoordinates v) := by
  rw [binaryMatrix_eq_toMatrix, LinearMap.toMatrix'_mulVec]
  change _ = binaryCoordinates (adjointBinary _
    (binaryCoordinates.symm (binaryCoordinates v)))
  rw [binaryCoordinates.symm_apply_apply]

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.LocalBlocks
