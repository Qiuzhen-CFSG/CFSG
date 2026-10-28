module

public import Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction
import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# Ordered triples on the projective line

A projective linear transformation is uniquely determined by the images of
zero, one, and infinity, and every ordered triple of distinct points occurs.
The inverse construction uses two-by-two determinants of homogeneous vectors.
Its determinant is the product of the three pairwise determinants; thus the
formula works in every characteristic. These are the point and coordinate
calculations for Borel, *Linear Algebraic Groups*, §10.8. Regularity in a family
is proved separately, rather than inferred from the point bijection. The private
coordinate bodies from the concrete action are imported for these internal
homogeneous-coordinate calculations; its public boundary stays unchanged.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
local instance : MulAction (Variety.Point (pgl2Variety (k := k)))
    (Point (projectiveLine k)) := pgl2ProjectiveLinePointMulAction

lemma pgl2_fixed_triple_eq_one (g : Variety.Point (pgl2Variety (k := k)))
    (h0 : g • (projectiveLineZero (k := k)) = (projectiveLineZero (k := k)))
    (h1 : g • (projectiveLineOne (k := k)) = (projectiveLineOne (k := k)))
    (hi : g • (projectiveLineInfinity (k := k)) = (projectiveLineInfinity (k := k))) : g = 1 := by
  obtain ⟨M, hM⟩ := Matrix.ProjGenLinGroup.mk_surjective (pgl2PointMulEquiv g)
  have h01 := (mem_pgl2ZeroStabilizer_iff g M hM).mp h0
  have h10 := (mem_pgl2InfinityStabilizer_iff g M hM).mp hi
  have hd := (mem_pgl2OneStabilizer_iff g M hM).mp h1
  simp only [h01, h10, add_zero, zero_add] at hd
  have hscalar : (M : Matrix (Fin 2) (Fin 2) k) = Matrix.scalar (Fin 2) (M.1 0 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar, Matrix.diagonal, h01, h10, hd]
  have hn : M.1 0 0 ≠ 0 := by
    intro hz
    have hdet := M.isUnit.map Matrix.detMonoidHom
    rw [hscalar, hz] at hdet
    simpa using hdet.ne_zero
  apply (pgl2PointMulEquiv (k := k)).injective
  rw [map_one, ← hM, Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 (M.1 0 0) hn, ?_⟩
  apply Units.ext
  simpa [Matrix.GeneralLinearGroup.coe_scalar] using hscalar.symm

lemma pgl2_triple_images_injective (g h : Variety.Point (pgl2Variety (k := k)))
    (h0 : g • (projectiveLineZero (k := k)) = h • (projectiveLineZero (k := k)))
    (h1 : g • (projectiveLineOne (k := k)) = h • (projectiveLineOne (k := k)))
    (hi : g • (projectiveLineInfinity (k := k)) = h • (projectiveLineInfinity (k := k))) : g = h := by
  have he : h⁻¹ * g = 1 := pgl2_fixed_triple_eq_one _
    (by rw [mul_smul, h0, inv_smul_smul])
    (by rw [mul_smul, h1, inv_smul_smul])
    (by rw [mul_smul, hi, inv_smul_smul])
  exact inv_mul_eq_one.mp he |>.symm
lemma projectiveLineAffinePoint_injective : Function.Injective (projectiveLineAffinePoint (k := k)) := by
  intro s t he
  have hp := congrArg (projectiveLinePointEquiv (k := k)) he
  simp only [projectiveLineAffinePoint, projectiveLinePointEquiv_projectivePointOfVector] at hp
  obtain ⟨r, hr⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hp
  have h1 := congrFun hr 1
  have h0 := congrFun hr 0
  simp only [projectiveLineAffineVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.cons_val_zero, mul_one] at h1 h0
  simpa [h1] using h0.symm

lemma projectiveLineInfinity_ne_affinePoint (t : k) :
    projectiveLineInfinity (k := k) ≠ projectiveLineAffinePoint t := by
  intro he
  have hp := congrArg (projectiveLinePointEquiv (k := k)) he
  simp only [projectiveLineInfinity, projectiveLineAffinePoint,
    projectiveLinePointEquiv_projectivePointOfVector] at hp
  obtain ⟨r, hr⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).mp hp
  have h1 := congrFun hr 1
  have h0 := congrFun hr 0
  simp only [projectiveLineAffineVector, projectiveLineInfinityVector, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero, mul_one] at h1 h0
  simp [h1] at h0

def detPair (v w : Fin 2 → k) : k := v 0 * w 1 - v 1 * w 0
omit [IsAlgClosed k] in
lemma detPair_ne_zero (v w : Fin 2 → k) (hv : v ≠ 0) (hw : w ≠ 0)
    (hne : Projectivization.mk k v hv ≠ Projectivization.mk k w hw) :
    detPair v w ≠ 0 := by
  intro hz
  apply hne
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  have he : v 0 * w 1 = v 1 * w 0 := sub_eq_zero.mp hz
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := by
      intro hh
      apply hw
      funext i
      fin_cases i <;> simp [h0, hh]
    refine ⟨v 1 / w 1, ?_⟩
    funext i
    fin_cases i
    · change v 1 / w 1 * w 0 = v 0
      rw [h0, mul_zero]
      exact (mul_eq_zero.mp (by simpa [h0] using he)).resolve_right h1 |>.symm
    · simp [h1]
  · refine ⟨v 0 / w 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · change v 0 / w 0 * w 1 = v 1
      rw [div_mul_eq_mul_div]
      exact (div_eq_iff h0).mpr he

def tripleMatrix (v0 v1 vi : Fin 2 → k) : Matrix (Fin 2) (Fin 2) k :=
  !![detPair v1 v0 * vi 0, detPair vi v1 * v0 0;
     detPair v1 v0 * vi 1, detPair vi v1 * v0 1]

omit [IsAlgClosed k] in
lemma tripleMatrix_det (v0 v1 vi : Fin 2 → k) :
    (tripleMatrix v0 v1 vi).det = detPair v1 v0 * detPair vi v1 * detPair vi v0 := by
  simp [tripleMatrix, Matrix.det_fin_two, detPair]
  ring

omit [IsAlgClosed k] in
lemma tripleMatrix_zero (v0 v1 vi : Fin 2 → k) :
    (tripleMatrix v0 v1 vi).mulVec (projectiveLineAffineVector 0) =
      detPair vi v1 • v0 := by
  funext i
  fin_cases i <;> simp [tripleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    projectiveLineAffineVector]

omit [IsAlgClosed k] in
lemma tripleMatrix_infinity (v0 v1 vi : Fin 2 → k) :
    (tripleMatrix v0 v1 vi).mulVec projectiveLineInfinityVector =
      detPair v1 v0 • vi := by
  funext i
  fin_cases i <;> simp [tripleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    projectiveLineInfinityVector]

omit [IsAlgClosed k] in
lemma tripleMatrix_one (v0 v1 vi : Fin 2 → k) :
    (tripleMatrix v0 v1 vi).mulVec (projectiveLineAffineVector 1) =
      detPair vi v0 • v1 := by
  funext i
  fin_cases i <;> simp [tripleMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    projectiveLineAffineVector, detPair] <;> ring

lemma exists_pgl2_of_distinct_points (p0 p1 pi : Point (projectiveLine k))
    (h10 : p1 ≠ p0) (hi1 : pi ≠ p1) (hi0 : pi ≠ p0) :
    ∃ g : Variety.Point (pgl2Variety (k := k)),
      g • projectiveLineZero (k := k) = p0 ∧
      g • projectiveLineOne (k := k) = p1 ∧
      g • projectiveLineInfinity (k := k) = pi := by
  let q := projectiveLinePointEquiv (k := k)
  let v0 := (q p0).rep
  let v1 := (q p1).rep
  let vi := (q pi).rep
  have hv0 : v0 ≠ 0 := (q p0).rep_nonzero
  have hv1 : v1 ≠ 0 := (q p1).rep_nonzero
  have hvi : vi ≠ 0 := (q pi).rep_nonzero
  have h01 : detPair v1 v0 ≠ 0 := detPair_ne_zero v1 v0 hv1 hv0 (by
    simpa [v0, v1] using fun hh => h10 (q.injective hh))
  have h1i : detPair vi v1 ≠ 0 := detPair_ne_zero vi v1 hvi hv1 (by
    simpa [vi, v1] using fun hh => hi1 (q.injective hh))
  have h0i : detPair vi v0 ≠ 0 := detPair_ne_zero vi v0 hvi hv0 (by
    simpa [vi, v0] using fun hh => hi0 (q.injective hh))
  have hd : (tripleMatrix v0 v1 vi).det ≠ 0 := by
    rw [tripleMatrix_det]
    exact mul_ne_zero (mul_ne_zero h01 h1i) h0i
  let M : GL (Fin 2) k := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd
  let g := (pgl2PointMulEquiv (k := k)).symm (Matrix.ProjGenLinGroup.mk M)
  have hM : Matrix.ProjGenLinGroup.mk M = pgl2PointMulEquiv g := by simp [g]
  refine ⟨g, ?_, ?_, ?_⟩
  · apply q.injective
    change projectiveLinePointEquiv (g • projectiveLineZero (k := k)) = q p0
    rw [projectiveLineZero, projectiveLineAffinePoint, pgl2ProjectiveLinePointMulAction_mk g M hM]
    rw [← Projectivization.mk_rep (q p0)]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    exact ⟨detPair vi v1, (tripleMatrix_zero v0 v1 vi).symm⟩
  · apply q.injective
    change projectiveLinePointEquiv (g • projectiveLineOne (k := k)) = q p1
    rw [projectiveLineOne, projectiveLineAffinePoint, pgl2ProjectiveLinePointMulAction_mk g M hM]
    rw [← Projectivization.mk_rep (q p1)]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    exact ⟨detPair vi v0, (tripleMatrix_one v0 v1 vi).symm⟩
  · apply q.injective
    change projectiveLinePointEquiv (g • projectiveLineInfinity (k := k)) = q pi
    rw [projectiveLineInfinity, pgl2ProjectiveLinePointMulAction_mk g M hM]
    rw [← Projectivization.mk_rep (q pi)]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    exact ⟨detPair v1 v0, (tripleMatrix_infinity v0 v1 vi).symm⟩


/-- The matrix realizing an ordered triple is unique in the actual PGL₂ carrier. -/
theorem existsUnique_pgl2_of_distinct_points (p0 p1 pi : Point (projectiveLine k))
    (h10 : p1 ≠ p0) (hi1 : pi ≠ p1) (hi0 : pi ≠ p0) :
    ∃! g : Variety.Point (pgl2Variety (k := k)),
      g • projectiveLineZero (k := k) = p0 ∧
      g • projectiveLineOne (k := k) = p1 ∧
      g • projectiveLineInfinity (k := k) = pi := by
  obtain ⟨g, h0, h1, hi⟩ := exists_pgl2_of_distinct_points p0 p1 pi h10 hi1 hi0
  refine ⟨g, ⟨h0, h1, hi⟩, ?_⟩
  rintro h ⟨hh0, hh1, hhi⟩
  exact pgl2_triple_images_injective h g (hh0.trans h0.symm)
    (hh1.trans h1.symm) (hhi.trans hi.symm)

end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
