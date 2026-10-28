module

public import Theory.AlgebraicGroup.Instance.LDU
public import Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.TypeASLDiagonalTorus

/-!
# The standard opposite-Borel open cell in `PGL2`

This module constructs the upper and lower root curves, their Weyl elements,
and the diagonal torus in the affine `PGL2` carrier.  Their closed images give
the standard unipotent and torus subgroups, while the already constructed
stabilizers of infinity and zero are the two standard opposite Borels.

For `d = 1 + a * b`, direct multiplication of determinant-one matrices proves
the regular exchange formula
`l(b)u(a) = u(a/d)h(d⁻¹)l(b/d)` when `d ≠ 0`.  On the divisor `d = 0`,
the same calculation gives
`l(-a⁻¹)u(a) = u(-a)n(a)`, with
`n(a) = u(a)l(-a⁻¹)u(a)` and `h(a) = n(a)n(-1)`.

The bottom-right-entry open locus of an `SL2` lift has a unique normalized
upper-diagonal-lower factorization.  Reversing the two matrix indices identifies
this condition with the leading-principal-minor open locus from the general
matrix LDU API.  After projection, the upper and lower coordinates remain
unique and the middle factor is unique as a `PGL2` torus point; this is the
correct scalar-invariant uniqueness statement.  The same nonvanishing entry
is the denominator condition placing the image of zero in the regular affine
chart of the constructed projective-line action.

The formulas follow Borel, *Linear Algebraic Groups*, §§13.13--13.14
(`refs/KGroup/Bor1/Chapter4.tex`), with scalar normalization made explicit at
the determinant-one lift.
-/

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public section

/-- The determinant-one matrix model used to normalize lifts into `PGL2`. -/
abbrev PGL2SLPoint := Matrix.SpecialLinearGroup (Fin 2) k

noncomputable def pgl2StandardProjection :
    AlgebraicGroup.Morphism (slVariety k 2) (pgl2Variety (k := k)) := by
  let pi := pgl2Projection (k := k)
  rw [Module.finrank_fin_fun k] at pi
  exact pi

noncomputable def pgl2SLPointProjection :
    PGL2SLPoint (k := k) →* Variety.Point (pgl2Variety (k := k)) := by
  exact (pgl2StandardProjection (k := k)).onPoints.comp
    (slPointMulEquiv (k := k) 2).symm.toMonoidHom

def pgl2UpperRootMatrix (a : k) : PGL2SLPoint (k := k) :=
  Matrix.SpecialLinearGroup.transvection zero_ne_one a

def pgl2LowerRootMatrix (b : k) : PGL2SLPoint (k := k) :=
  Matrix.SpecialLinearGroup.transvection one_ne_zero b

def pgl2WeylMatrix (a : k) (_ha : a ≠ 0) : PGL2SLPoint (k := k) :=
  pgl2UpperRootMatrix a * pgl2LowerRootMatrix (-a⁻¹) * pgl2UpperRootMatrix a

def pgl2TorusMatrix (a : k) (ha : a ≠ 0) : PGL2SLPoint (k := k) :=
  pgl2WeylMatrix a ha * pgl2WeylMatrix (-1) (neg_ne_zero.mpr one_ne_zero)

noncomputable def pgl2UpperRoot (a : k) : Variety.Point (pgl2Variety (k := k)) :=
  (pgl2UpperUnipotentMorphism (k := k)).onPoints (kPlusPoint a)

noncomputable def pgl2LowerRoot (b : k) : Variety.Point (pgl2Variety (k := k)) :=
  (pgl2LowerUnipotentMorphism (k := k)).onPoints (kPlusPoint b)

noncomputable def pgl2WeylElement (a : k) (_ha : a ≠ 0) :
    Variety.Point (pgl2Variety (k := k)) :=
  pgl2UpperRoot a * pgl2LowerRoot (-a⁻¹) * pgl2UpperRoot a

noncomputable def pgl2TorusElement (a : k) (ha : a ≠ 0) :
    Variety.Point (pgl2Variety (k := k)) :=
  pgl2WeylElement a ha * pgl2WeylElement (-1) (neg_ne_zero.mpr one_ne_zero)

noncomputable def pgl2StandardTorusMorphism :
    AlgebraicGroup.Morphism (dVariety k 1) (pgl2Variety (k := k)) :=
  (pgl2StandardProjection (k := k)).comp (typeASLDiagonalMorphism (k := k) 1)

noncomputable def pgl2TorusParameter (a : k) (ha : a ≠ 0) :
    Variety.Point (dVariety k 1) :=
  (dPointEquiv 1).symm (fun _ => Units.mk0 a ha)

lemma pgl2UpperRoot_eq (a : k) :
    pgl2UpperRoot (k := k) a = pgl2SLPointProjection (pgl2UpperRootMatrix a) := by
  change (pgl2StandardProjection (k := k)).onPoints
      (typeASLRootPoint 1 standardSL2UpperRootIndex a) = _
  have hx : typeASLRootPoint 1 standardSL2UpperRootIndex a =
      (slPointMulEquiv (k := k) 2).symm (pgl2UpperRootMatrix a) := by
    apply (slPointMulEquiv (k := k) 2).injective
    simp [typeASLRootPoint, pgl2UpperRootMatrix]
    congr
  rw [hx]
  rfl

lemma pgl2LowerRoot_eq (b : k) :
    pgl2LowerRoot (k := k) b = pgl2SLPointProjection (pgl2LowerRootMatrix b) := by
  change (pgl2StandardProjection (k := k)).onPoints
      (typeASLRootPoint 1 standardSL2LowerRootIndex b) = _
  have hx : typeASLRootPoint 1 standardSL2LowerRootIndex b =
      (slPointMulEquiv (k := k) 2).symm (pgl2LowerRootMatrix b) := by
    apply (slPointMulEquiv (k := k) 2).injective
    simp [typeASLRootPoint, pgl2LowerRootMatrix]
    congr
  rw [hx]
  rfl

lemma pgl2WeylElement_eq (a : k) (ha : a ≠ 0) :
    pgl2WeylElement (k := k) a ha = pgl2SLPointProjection (pgl2WeylMatrix a ha) := by
  simp [pgl2WeylElement, pgl2WeylMatrix, pgl2UpperRoot_eq, pgl2LowerRoot_eq]

lemma pgl2TorusElement_eq (a : k) (ha : a ≠ 0) :
    pgl2TorusElement (k := k) a ha = pgl2SLPointProjection (pgl2TorusMatrix a ha) := by
  simp [pgl2TorusElement, pgl2TorusMatrix, pgl2WeylElement_eq]

omit [IsAlgClosed k] in
lemma pgl2TorusMatrix_eq_diag2 (a : k) (ha : a ≠ 0) :
    pgl2TorusMatrix a ha = Matrix.SpecialLinearGroup.diag2 a ha := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2TorusMatrix, pgl2WeylMatrix, pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe', ha]

lemma pgl2StandardTorusMorphism_parameter (a : k) (ha : a ≠ 0) :
    (pgl2StandardTorusMorphism (k := k)).onPoints (pgl2TorusParameter a ha) =
      pgl2TorusElement a ha := by
  rw [pgl2TorusElement_eq, pgl2TorusMatrix_eq_diag2]
  change (pgl2StandardProjection (k := k)).onPoints
      ((typeASLDiagonalMorphism (k := k) 1).onPoints
        (pgl2TorusParameter a ha)) =
    pgl2SLPointProjection (Matrix.SpecialLinearGroup.diag2 a ha)
  have hzero : (typeASLDiagonalEntries 1 (pgl2TorusParameter a ha) 0 : k) = a := by
    rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl,
      typeASLDiagonalEntries_castSucc]
    rfl
  have hone : (typeASLDiagonalEntries 1 (pgl2TorusParameter a ha) 1 : k) = a⁻¹ := by
    rw [show (1 : Fin 2) = Fin.last 1 by rfl, typeASLDiagonalEntries_last]
    have hp : (dPointEquiv 1) (pgl2TorusParameter a ha) =
        (fun _ => Units.mk0 a ha) :=
      (dPointEquiv 1).apply_symm_apply _
    rw [hp]
    simp
  have hx : (typeASLDiagonalMorphism (k := k) 1).onPoints
      (pgl2TorusParameter a ha) =
        (slPointMulEquiv (k := k) 2).symm
          (Matrix.SpecialLinearGroup.diag2 a ha) := by
    apply (slPointEquiv (k := k) 2).injective
    have he : (slPointMulEquiv (k := k) 2).symm
        (Matrix.SpecialLinearGroup.diag2 a ha) =
      (slPointEquiv (k := k) 2).symm
        (Matrix.SpecialLinearGroup.diag2 a ha) := by
      apply (slPointEquiv (k := k) 2).injective
      rw [← slPointMulEquiv_apply]
      exact (slPointMulEquiv (k := k) 2).apply_symm_apply _
    rw [he]
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change slPointMatrix 2
        ((typeASLDiagonalMorphism (k := k) 1).onPoints
          (pgl2TorusParameter a ha)) =
      (Matrix.SpecialLinearGroup.diag2 a ha).1
    rw [typeASLDiagonalMorphism_matrix]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [typeASLDiagonalMatrix, hzero, hone,
        Matrix.SpecialLinearGroup.diag2_coe']
  rw [hx]
  rfl

omit [IsAlgClosed k] in
/-- The exact determinant-one matrix exchange on the regular rank-one cell. -/
lemma sl2_regular_relation (a b : k) (h : 1 + a * b ≠ 0) :
    pgl2LowerRootMatrix (k := k) b * pgl2UpperRootMatrix a =
      pgl2UpperRootMatrix (a / (1 + a * b)) *
        Matrix.SpecialLinearGroup.diag2 ((1 + a * b)⁻¹) (inv_ne_zero h) *
          pgl2LowerRootMatrix (b / (1 + a * b)) := by
  have h' : 1 + b * a ≠ 0 := by simpa [mul_comm] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe', h]
  all_goals field_simp [h, h']
  all_goals ring

omit [IsAlgClosed k] in
/-- The exact determinant-one matrix exchange on the singular rank-one divisor. -/
lemma sl2_singular_relation (a : k) (ha : a ≠ 0) :
    pgl2LowerRootMatrix (k := k) (-a⁻¹) * pgl2UpperRootMatrix a =
      pgl2UpperRootMatrix (-a) * pgl2WeylMatrix a ha := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2WeylMatrix, pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, ha]

lemma pgl2_regular_relation (a b : k) (h : 1 + a * b ≠ 0) :
    pgl2LowerRoot (k := k) b * pgl2UpperRoot a =
      pgl2UpperRoot (a / (1 + a * b)) *
        pgl2TorusElement ((1 + a * b)⁻¹) (inv_ne_zero h) *
          pgl2LowerRoot (b / (1 + a * b)) := by
  simp only [pgl2UpperRoot_eq, pgl2LowerRoot_eq, pgl2TorusElement_eq, ← map_mul]
  apply congrArg pgl2SLPointProjection
  rw [pgl2TorusMatrix_eq_diag2]
  have h' : 1 + b * a ≠ 0 := by simpa [mul_comm] using h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe', h]
  all_goals field_simp [h, h']
  all_goals ring

lemma pgl2_singular_relation (a : k) (ha : a ≠ 0) :
    pgl2LowerRoot (k := k) (-a⁻¹) * pgl2UpperRoot a =
      pgl2UpperRoot (-a) * pgl2WeylElement a ha := by
  simp only [pgl2UpperRoot_eq, pgl2LowerRoot_eq, pgl2WeylElement_eq, ← map_mul]
  apply congrArg pgl2SLPointProjection
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2WeylMatrix, pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, ha]

omit [IsAlgClosed k] in
lemma sl2_open_cell_factorization (A : PGL2SLPoint (k := k)) (hA : A.1 1 1 ≠ 0) :
    A = pgl2UpperRootMatrix (A.1 0 1 / A.1 1 1) *
        Matrix.SpecialLinearGroup.diag2 (A.1 1 1)⁻¹ (inv_ne_zero hA) *
          pgl2LowerRootMatrix (A.1 1 0 / A.1 1 1) := by
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    have hdet' := A.2
    rw [Matrix.det_fin_two] at hdet'
    exact hdet'
  have h00 : A.1 0 0 = (A.1 1 1)⁻¹ +
      A.1 0 1 * (A.1 1 0 / A.1 1 1) := by
    calc
      A.1 0 0 = (1 + A.1 0 1 * A.1 1 0) / A.1 1 1 := by
        apply (eq_div_iff hA).2
        linear_combination hdet
      _ = (A.1 1 1)⁻¹ + A.1 0 1 * (A.1 1 0 / A.1 1 1) := by
        field_simp [hA]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pgl2UpperRootMatrix, pgl2LowerRootMatrix,
      Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe', hA]
  · exact h00
  all_goals field_simp [hA]

lemma pgl2_open_cell_factorization_of_lift (A : PGL2SLPoint (k := k)) (hA : A.1 1 1 ≠ 0) :
    pgl2SLPointProjection A =
      pgl2UpperRoot (A.1 0 1 / A.1 1 1) *
        pgl2TorusElement (A.1 1 1)⁻¹ (inv_ne_zero hA) *
          pgl2LowerRoot (A.1 1 0 / A.1 1 1) := by
  rw [pgl2UpperRoot_eq, pgl2LowerRoot_eq, pgl2TorusElement_eq,
    ← map_mul, ← map_mul]
  congr 1
  rw [pgl2TorusMatrix_eq_diag2]
  exact sl2_open_cell_factorization A hA

omit [IsAlgClosed k] in
lemma sl2_open_cell_coordinates_unique
    (a b a' b' : k) (t t' : kˣ)
    (h : pgl2UpperRootMatrix a *
          Matrix.SpecialLinearGroup.diag2 t.1 t.ne_zero * pgl2LowerRootMatrix b =
        pgl2UpperRootMatrix a' *
          Matrix.SpecialLinearGroup.diag2 t'.1 t'.ne_zero * pgl2LowerRootMatrix b') :
    a = a' ∧ t = t' ∧ b = b' := by
  have h11 := congrArg (fun A : PGL2SLPoint (k := k) => A.1 1 1) h
  have h01 := congrArg (fun A : PGL2SLPoint (k := k) => A.1 0 1) h
  have h10 := congrArg (fun A : PGL2SLPoint (k := k) => A.1 1 0) h
  simp [pgl2UpperRootMatrix, pgl2LowerRootMatrix,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe'] at h11 h01 h10
  have ht : t = t' := by
    apply Units.ext
    exact h11
  subst t'
  constructor
  · exact (mul_right_cancel₀ (inv_ne_zero t.ne_zero) h01)
  · exact ⟨rfl, mul_left_cancel₀ (inv_ne_zero t.ne_zero) h10⟩

def pgl2OpenCellReverseMatrix (A : Matrix (Fin 2) (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k :=
  Matrix.reindexAlgEquiv k k (Equiv.swap (0 : Fin 2) 1) A

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseMatrix_apply (A : Matrix (Fin 2) (Fin 2) k) (i j : Fin 2) :
    pgl2OpenCellReverseMatrix A i j = A (Equiv.swap (0 : Fin 2) 1 i)
      (Equiv.swap (0 : Fin 2) 1 j) := by
  rfl

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseMatrix_hasNonzeroLeadingPrincipalMinors
    (A : PGL2SLPoint (k := k)) (hA : A.1 1 1 ≠ 0) :
    HasNonzeroLeadingPrincipalMinors (pgl2OpenCellReverseMatrix A.1) := by
  intro r hr hpos
  have hrange : r = 1 ∨ r = 2 := by omega
  rcases hrange with rfl | rfl
  · simpa [leadingPrincipalMinor, leadingPrincipalSubmatrix,
      pgl2OpenCellReverseMatrix_apply, Matrix.det_fin_one]
  · have hdet : Matrix.det (pgl2OpenCellReverseMatrix A.1) = Matrix.det A.1 := by
      exact Matrix.det_reindexAlgEquiv (R := k) k (Equiv.swap (0 : Fin 2) 1) A.1
    change Matrix.det (pgl2OpenCellReverseMatrix A.1) ≠ 0
    rw [hdet, A.2]
    exact one_ne_zero

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseMatrix_ldu_unique
    (A : PGL2SLPoint (k := k)) (hA : A.1 1 1 ≠ 0) :
    ∃! F : LDUFactors (k := k) 2,
      F.multiply = pgl2OpenCellReverseMatrix A.1 := by
  rw [exists_unique_ldu_iff]
  exact pgl2OpenCellReverseMatrix_hasNonzeroLeadingPrincipalMinors A hA

def pgl2OpenCellReverseSL2 (A : PGL2SLPoint (k := k)) : PGL2SLPoint (k := k) :=
  ⟨pgl2OpenCellReverseMatrix A.1, by
    calc
      Matrix.det (pgl2OpenCellReverseMatrix A.1) = Matrix.det A.1 := by
        exact Matrix.det_reindexAlgEquiv (R := k) k
          (Equiv.swap (0 : Fin 2) 1) A.1
      _ = 1 := A.2⟩

noncomputable def pgl2OpenCellReverseGLPoint (A : PGL2SLPoint (k := k)) :
    Variety.Point (glVariety (k := k) 2) :=
  (glPointEquiv 2).symm
    (Matrix.SpecialLinearGroup.toGL (pgl2OpenCellReverseSL2 A))

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseGLPoint_matrix (A : PGL2SLPoint (k := k)) :
    glMatrixOfPoint 2 (pgl2OpenCellReverseGLPoint A) = pgl2OpenCellReverseMatrix A.1 := by
  have h := (glPointEquiv (k := k) 2).apply_symm_apply
    (Matrix.SpecialLinearGroup.toGL (pgl2OpenCellReverseSL2 A))
  exact congrArg (fun B : GL (Fin 2) k => B.1) h

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseGLPoint_mem_principalOpen_iff
    (A : PGL2SLPoint (k := k)) :
    pgl2OpenCellReverseGLPoint A ∈ glLduPrincipalOpenLocus (k := k) 2 ↔
      A.1 1 1 ≠ 0 := by
  rw [mem_glLduPrincipalOpenLocus_iff,
    pgl2OpenCellReverseGLPoint_matrix]
  constructor
  · intro h
    have h1 := h 1 (by omega) (by omega)
    simpa [leadingPrincipalMinor, leadingPrincipalSubmatrix,
      pgl2OpenCellReverseMatrix_apply, Matrix.det_fin_one] using h1
  · exact pgl2OpenCellReverseMatrix_hasNonzeroLeadingPrincipalMinors A

omit [IsAlgClosed k] in
lemma pgl2OpenCellReverseGLPoint_mem_principalOpen_iff_lduRange
    (A : PGL2SLPoint (k := k)) :
    pgl2OpenCellReverseGLPoint A ∈ glLduPrincipalOpenLocus (k := k) 2 ↔
      pgl2OpenCellReverseMatrix A.1 ∈
        Set.range (LDUFactors.multiply (k := k) (n := 2)) := by
  rw [mem_glLduPrincipalOpenLocus_iff_lduRange,
    pgl2OpenCellReverseGLPoint_matrix]

noncomputable def pgl2UpperUnipotentClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2UpperUnipotentMorphism (k := k)).imageClosedSubgroup

noncomputable def pgl2LowerUnipotentClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2LowerUnipotentMorphism (k := k)).imageClosedSubgroup

noncomputable def pgl2StandardTorusClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2StandardTorusMorphism (k := k)).imageClosedSubgroup

lemma pgl2StandardTorusClosed_isSubtorus :
    IsSubtorus (pgl2StandardTorusClosed (k := k)) := by
  exact morphism_image_isTorus (pgl2StandardTorusMorphism (k := k))
    (dVariety_isTorus 1)

def pgl2OppositeOpenCell : Set (Variety.Point (pgl2Variety (k := k))) :=
  {g | ∃ A : PGL2SLPoint (k := k),
    pgl2SLPointProjection A = g ∧ A.1 1 1 ≠ 0}

lemma pgl2OppositeOpenCell_iff_factorization
    (g : Variety.Point (pgl2Variety (k := k))) :
    g ∈ pgl2OppositeOpenCell (k := k) ↔
      ∃ (a b : k) (t : kˣ),
        g = pgl2UpperRoot a * pgl2TorusElement t.1 t.ne_zero *
          pgl2LowerRoot b := by
  constructor
  · rintro ⟨A, rfl, hA⟩
    refine ⟨A.1 0 1 / A.1 1 1, A.1 1 0 / A.1 1 1,
      Units.mk0 (A.1 1 1)⁻¹ (inv_ne_zero hA), ?_⟩
    simpa using pgl2_open_cell_factorization_of_lift A hA
  · rintro ⟨a, b, t, rfl⟩
    refine ⟨pgl2UpperRootMatrix a *
      Matrix.SpecialLinearGroup.diag2 t.1 t.ne_zero * pgl2LowerRootMatrix b, ?_, ?_⟩
    · simp [pgl2UpperRoot_eq, pgl2LowerRoot_eq, pgl2TorusElement_eq,
        pgl2TorusMatrix_eq_diag2]
    · simp [pgl2UpperRootMatrix, pgl2LowerRootMatrix,
        Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe']

private lemma pgl2Morphism_cast_onPoints
    {m n : Nat} (h : m = n)
    (f : AlgebraicGroup.Morphism (slVariety k m) (pgl2Variety (k := k)))
    (x : Variety.Point (slVariety k n)) :
    f.onPoints ((congrArg (slVariety k) h).symm ▸ x) =
      ((congrArg (fun q => AlgebraicGroup.Morphism (slVariety k q)
        (pgl2Variety (k := k))) h) ▸ f).onPoints x := by
  subst n
  rfl

omit [IsAlgClosed k] in
private lemma pgl2Cast_toPGL {m n : Nat} (h : m = n)
    (A : Matrix.SpecialLinearGroup (Fin n) k) :
    let c : Matrix.ProjGenLinGroup (Fin m) k ≃* Matrix.ProjGenLinGroup (Fin n) k := by
      rw [h]
    c (Matrix.SpecialLinearGroup.toPGL
      ((congrArg (fun q => Matrix.SpecialLinearGroup (Fin q) k) h).symm ▸ A)) =
      Matrix.SpecialLinearGroup.toPGL A := by
  subst n
  rfl

private lemma pgl2SLPointEquiv_cast {m n : Nat} (h : m = n)
    (A : Matrix.SpecialLinearGroup (Fin n) k) :
    slPointEquiv m
        ((congrArg (slVariety k) h).symm ▸
          ((slPointMulEquiv (k := k) n).symm A)) =
      (congrArg (fun q => Matrix.SpecialLinearGroup (Fin q) k) h).symm ▸ A := by
  cases h
  simp only
  rw [← slPointMulEquiv_apply]
  exact (slPointMulEquiv (k := k) m).apply_symm_apply A

lemma pgl2SLPointProjection_class (A : PGL2SLPoint (k := k)) :
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) =
      pgl2PointMulEquiv (k := k) (pgl2SLPointProjection A) := by
  have hn : Module.finrank k (Fin 2 → k) = 2 := Module.finrank_fin_fun k
  let x : Variety.Point (slVariety k (Module.finrank k (Fin 2 → k))) :=
    (congrArg (slVariety k) hn).symm ▸
      ((slPointMulEquiv (k := k) 2).symm A)
  calc
    Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL A) =
        pgl2SLPointClass x := by
      unfold pgl2SLPointClass
      rw [show slPointEquiv (Module.finrank k (Fin 2 → k)) x =
          (congrArg (fun q => Matrix.SpecialLinearGroup (Fin q) k) hn).symm ▸ A by
        exact pgl2SLPointEquiv_cast hn A]
      exact (pgl2Cast_toPGL hn A).symm
    _ = pgl2PointMulEquiv (k := k)
        ((pgl2Projection (k := k)).onPoints x) :=
      (pgl2PointMulEquiv_projection x).symm
    _ = pgl2PointMulEquiv (k := k) (pgl2SLPointProjection A) := by
      congr 1
      unfold pgl2SLPointProjection pgl2StandardProjection
      exact pgl2Morphism_cast_onPoints hn
        (pgl2Projection (k := k)) ((slPointMulEquiv (k := k) 2).symm A)

/-- The upper root curve lies in the standard Borel stabilizing infinity. -/
lemma pgl2UpperRoot_mem_upperBorel (a : k) :
    pgl2UpperRoot (k := k) a ∈ pgl2UpperBorel (k := k) := by
  have hrep : Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL (pgl2UpperRootMatrix a)) =
        pgl2PointMulEquiv (k := k) (pgl2UpperRoot a) := by
    rw [pgl2UpperRoot_eq]
    exact pgl2SLPointProjection_class _
  rw [mem_pgl2InfinityStabilizer_iff
    (pgl2UpperRoot a) (Matrix.SpecialLinearGroup.toGL
      (pgl2UpperRootMatrix a)) hrep]
  simp [pgl2UpperRootMatrix,
    Matrix.SpecialLinearGroup.transvection_coe]

/-- The lower root curve lies in the opposite Borel stabilizing zero. -/
lemma pgl2LowerRoot_mem_lowerBorel (b : k) :
    pgl2LowerRoot (k := k) b ∈ pgl2LowerBorel (k := k) := by
  have hrep : Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL (pgl2LowerRootMatrix b)) =
        pgl2PointMulEquiv (k := k) (pgl2LowerRoot b) := by
    rw [pgl2LowerRoot_eq]
    exact pgl2SLPointProjection_class _
  rw [mem_pgl2ZeroStabilizer_iff
    (pgl2LowerRoot b) (Matrix.SpecialLinearGroup.toGL
      (pgl2LowerRootMatrix b)) hrep]
  simp [pgl2LowerRootMatrix,
    Matrix.SpecialLinearGroup.transvection_coe]

/-- Every standard torus point lies in the upper Borel. -/
lemma pgl2TorusElement_mem_upperBorel (a : k) (ha : a ≠ 0) :
    pgl2TorusElement (k := k) a ha ∈ pgl2UpperBorel (k := k) := by
  have hrep : Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL (pgl2TorusMatrix a ha)) =
        pgl2PointMulEquiv (k := k) (pgl2TorusElement a ha) := by
    rw [pgl2TorusElement_eq]
    exact pgl2SLPointProjection_class _
  rw [mem_pgl2InfinityStabilizer_iff
    (pgl2TorusElement a ha) (Matrix.SpecialLinearGroup.toGL
      (pgl2TorusMatrix a ha)) hrep, pgl2TorusMatrix_eq_diag2]
  simp [Matrix.SpecialLinearGroup.diag2_coe']

/-- Every standard torus point lies in the lower Borel. -/
lemma pgl2TorusElement_mem_lowerBorel (a : k) (ha : a ≠ 0) :
    pgl2TorusElement (k := k) a ha ∈ pgl2LowerBorel (k := k) := by
  have hrep : Matrix.ProjGenLinGroup.mk
      (Matrix.SpecialLinearGroup.toGL (pgl2TorusMatrix a ha)) =
        pgl2PointMulEquiv (k := k) (pgl2TorusElement a ha) := by
    rw [pgl2TorusElement_eq]
    exact pgl2SLPointProjection_class _
  rw [mem_pgl2ZeroStabilizer_iff
    (pgl2TorusElement a ha) (Matrix.SpecialLinearGroup.toGL
      (pgl2TorusMatrix a ha)) hrep, pgl2TorusMatrix_eq_diag2]
  simp [Matrix.SpecialLinearGroup.diag2_coe']

/-- The closed upper-unipotent image is contained in the upper Borel. -/
lemma pgl2UpperUnipotentClosed_le_upperBorel :
    pgl2UpperUnipotentClosed (k := k) ≤ pgl2UpperBorelClosed (k := k) := by
  intro g hg
  change g ∈ (pgl2UpperUnipotentMorphism (k := k)).image at hg
  obtain ⟨x, rfl⟩ := hg
  rw [← kPlusPoint_coordinate x]
  change pgl2UpperRoot (k := k)
      (Multiplicative.toAdd (additiveGroupPointEquiv k x)) ∈
    (pgl2UpperBorelClosed (k := k)).toSubgroup
  rw [pgl2InfinityStabilizerClosed_toSubgroup]
  exact pgl2UpperRoot_mem_upperBorel (k := k)
    (Multiplicative.toAdd (additiveGroupPointEquiv k x))

/-- The closed lower-unipotent image is contained in the lower Borel. -/
lemma pgl2LowerUnipotentClosed_le_lowerBorel :
    pgl2LowerUnipotentClosed (k := k) ≤ pgl2LowerBorelClosed (k := k) := by
  intro g hg
  change g ∈ (pgl2LowerUnipotentMorphism (k := k)).image at hg
  obtain ⟨x, rfl⟩ := hg
  rw [← kPlusPoint_coordinate x]
  change pgl2LowerRoot (k := k)
      (Multiplicative.toAdd (additiveGroupPointEquiv k x)) ∈
    (pgl2LowerBorelClosed (k := k)).toSubgroup
  rw [pgl2ZeroStabilizerClosed_toSubgroup]
  exact pgl2LowerRoot_mem_lowerBorel (k := k)
    (Multiplicative.toAdd (additiveGroupPointEquiv k x))

omit [IsAlgClosed k] in
private lemma pgl2TorusParameter_coordinate
    (x : Variety.Point (dVariety k 1)) :
    pgl2TorusParameter
        (((dPointEquiv 1) x 0 : k))
        (Units.ne_zero ((dPointEquiv 1) x 0)) = x := by
  apply (dPointEquiv 1).injective
  change (dPointEquiv 1) ((dPointEquiv 1).symm
    (fun _ => Units.mk0 (((dPointEquiv 1) x 0 : k))
      (Units.ne_zero ((dPointEquiv 1) x 0)))) = (dPointEquiv 1) x
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i
  apply Units.ext
  rfl

/-- The standard torus closed image is contained in the upper Borel. -/
lemma pgl2StandardTorusClosed_le_upperBorel :
    pgl2StandardTorusClosed (k := k) ≤ pgl2UpperBorelClosed (k := k) := by
  intro g hg
  change g ∈ (pgl2StandardTorusMorphism (k := k)).image at hg
  obtain ⟨x, rfl⟩ := hg
  rw [← pgl2TorusParameter_coordinate x,
    pgl2StandardTorusMorphism_parameter]
  change pgl2TorusElement (k := k) _ _ ∈
    (pgl2UpperBorelClosed (k := k)).toSubgroup
  rw [pgl2InfinityStabilizerClosed_toSubgroup]
  exact pgl2TorusElement_mem_upperBorel _ _

/-- The standard torus closed image is contained in the lower Borel. -/
lemma pgl2StandardTorusClosed_le_lowerBorel :
    pgl2StandardTorusClosed (k := k) ≤ pgl2LowerBorelClosed (k := k) := by
  intro g hg
  change g ∈ (pgl2StandardTorusMorphism (k := k)).image at hg
  obtain ⟨x, rfl⟩ := hg
  rw [← pgl2TorusParameter_coordinate x,
    pgl2StandardTorusMorphism_parameter]
  change pgl2TorusElement (k := k) _ _ ∈
    (pgl2LowerBorelClosed (k := k)).toSubgroup
  rw [pgl2ZeroStabilizerClosed_toSubgroup]
  exact pgl2TorusElement_mem_lowerBorel _ _

lemma pgl2OppositeOpenCell_action_affine_chart
    (A : PGL2SLPoint (k := k)) (hA : A.1 1 1 ≠ 0) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    pgl2SLPointProjection A • projectiveLineAffinePoint 0 =
      projectiveLineAffinePoint (A.1 0 1 / A.1 1 1) := by
  have hden : (Matrix.SpecialLinearGroup.toGL A).1 1 0 * 0 +
      (Matrix.SpecialLinearGroup.toGL A).1 1 1 ≠ 0 := by
    simpa using hA
  simpa only [mul_zero, zero_add,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using
    (pgl2ProjectiveLinePointMulAction_affine_chart
      (k := k) (pgl2SLPointProjection A)
      (Matrix.SpecialLinearGroup.toGL A)
      (pgl2SLPointProjection_class A) 0 hden)

noncomputable def pgl2OpenCellMatrix (a b : k) (t : kˣ) : PGL2SLPoint (k := k) :=
  pgl2UpperRootMatrix a *
    Matrix.SpecialLinearGroup.diag2 t.1 t.ne_zero * pgl2LowerRootMatrix b

lemma pgl2OpenCellFactor_eq_projection (a b : k) (t : kˣ) :
    pgl2UpperRoot (k := k) a * pgl2TorusElement t.1 t.ne_zero *
        pgl2LowerRoot b =
      pgl2SLPointProjection (pgl2OpenCellMatrix a b t) := by
  simp [pgl2OpenCellMatrix, pgl2UpperRoot_eq, pgl2LowerRoot_eq,
    pgl2TorusElement_eq, pgl2TorusMatrix_eq_diag2]

lemma pgl2OpenCell_factor_unique
    (a b a' b' : k) (t t' : kˣ)
    (h : pgl2UpperRoot (k := k) a * pgl2TorusElement t.1 t.ne_zero *
          pgl2LowerRoot b =
        pgl2UpperRoot a' * pgl2TorusElement t'.1 t'.ne_zero *
          pgl2LowerRoot b') :
    a = a' ∧ pgl2TorusElement (k := k) t.1 t.ne_zero =
      pgl2TorusElement t'.1 t'.ne_zero ∧ b = b' := by
  have hfactor := h
  rw [pgl2OpenCellFactor_eq_projection,
    pgl2OpenCellFactor_eq_projection] at h
  have hp := congrArg (pgl2PointMulEquiv (k := k)) h
  rw [← pgl2SLPointProjection_class,
    ← pgl2SLPointProjection_class] at hp
  obtain ⟨c, hc⟩ :=
    (Matrix.ProjGenLinGroup.mk_eq_mk_iff).1 hp
  have hc11 := congrArg (fun A : GL (Fin 2) k => A.1 1 1) hc
  have hc01 := congrArg (fun A : GL (Fin 2) k => A.1 0 1) hc
  have hc10 := congrArg (fun A : GL (Fin 2) k => A.1 1 0) hc
  simp [pgl2OpenCellMatrix, pgl2UpperRootMatrix, pgl2LowerRootMatrix,
    Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.SpecialLinearGroup.diag2_coe'] at hc11 hc01 hc10
  have ha : a = a' := by
    apply mul_right_cancel₀ (inv_ne_zero t'.ne_zero)
    calc
      a * (t'.1)⁻¹ = a * ((t.1)⁻¹ * c.1) := by rw [hc11]
      _ = a * (t.1)⁻¹ * c.1 := by ring
      _ = a' * (t'.1)⁻¹ := hc01
  have hb : b = b' := by
    apply mul_left_cancel₀ (inv_ne_zero t'.ne_zero)
    calc
      (t'.1)⁻¹ * b = ((t.1)⁻¹ * c.1) * b := by rw [hc11]
      _ = (t.1)⁻¹ * b * c.1 := by ring
      _ = (t'.1)⁻¹ * b' := hc10
  subst a'
  subst b'
  refine ⟨rfl, ?_, rfl⟩
  exact mul_left_cancel (mul_right_cancel hfactor)

end

end Theory.AlgebraicGroup.Variety.Geometric
