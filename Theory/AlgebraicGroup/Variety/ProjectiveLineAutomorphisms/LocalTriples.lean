module
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.SectionMatrices
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.Triples
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.OpenFactorization
public import Theory.AlgebraicGroup.Instance.PGL2GeneralLinearProjection
import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# The regular inverse on triples in projective affine charts

For three varying distinct points, each in a prescribed standard chart, pull
back their affine coordinates to global sections. Two-by-two determinants
construct the unique realizing matrix; its determinant is nowhere zero.
The global-section matrix construction and the genuine GL₂-to-PGL₂ projection
therefore give a geometric map with the three exact prescribed images.

This is the local formula for the inverse of the triple orbit map in Borel,
*Linear Algebraic Groups*, §10.8. Both charts and all characteristics are used.
The internal concrete action import supplies its homogeneous-coordinate
bodies without changing that module's public boundary.
-/

open scoped MatrixGroups
open CategoryTheory AlgebraicGeometry
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section
local instance localTriplePgl2Action : MulAction (Variety.Point (pgl2Variety (k := k)))
    (Point (projectiveLine k)) := pgl2ProjectiveLinePointMulAction

private def chartSections {V : Geometric k} (i : Fin 2)
    (f : Morphism V (polynomialAffineLine k)) : Fin 2 → Γ(V.toScheme, ⊤) :=
  fun j => if j = i then 1 else affineCoordinateSection f

omit [IsAlgClosed k] in
private lemma chartSections_evaluation {V : Geometric k} (i : Fin 2)
    (f : Morphism V (polynomialAffineLine k)) (x : Point V) (j : Fin 2) :
    sectionEvaluation V x (chartSections i f j) =
      chartVector i (sectionEvaluation V x (affineCoordinateSection f)) j := by
  by_cases hj : j = i <;> simp [chartSections, chartVector, hj]

private def localTripleMatrix {V : Geometric k} (i0 i1 ii : Fin 2)
    (f0 f1 fi : Morphism V (polynomialAffineLine k)) : Matrix (Fin 2) (Fin 2) Γ(V.toScheme, ⊤) :=
  let v0 := chartSections i0 f0
  let v1 := chartSections i1 f1
  let vi := chartSections ii fi
  let d10 := v1 0 * v0 1 - v1 1 * v0 0
  let di1 := vi 0 * v1 1 - vi 1 * v1 0
  !![d10 * vi 0, di1 * v0 0; d10 * vi 1, di1 * v0 1]

omit [IsAlgClosed k] in
private lemma localTripleMatrix_evaluation {V : Geometric k} (i0 i1 ii : Fin 2)
    (f0 f1 fi : Morphism V (polynomialAffineLine k)) (x : Point V) :
    (localTripleMatrix i0 i1 ii f0 f1 fi).map (sectionEvaluation V x) =
      tripleMatrix
        (chartVector i0 (sectionEvaluation V x (affineCoordinateSection f0)))
        (chartVector i1 (sectionEvaluation V x (affineCoordinateSection f1)))
        (chartVector ii (sectionEvaluation V x (affineCoordinateSection fi))) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [localTripleMatrix, Matrix.map_apply, tripleMatrix, detPair, chartSections_evaluation]

private lemma chartTriple_det_ne_zero {V : Geometric k} (i0 i1 ii : Fin 2)
    (f0 f1 fi : Morphism V (polynomialAffineLine k))
    (h10 : ∀ x, projectiveLineChartInclusion i1 (f1 x) ≠ projectiveLineChartInclusion i0 (f0 x))
    (hi1 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i1 (f1 x))
    (hi0 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i0 (f0 x))
    (x : Point V) : (localTripleMatrix i0 i1 ii f0 f1 fi |>.map (sectionEvaluation V x)).det ≠ 0 := by
  have hn (a b : Fin 2) (fa fb : Morphism V (polynomialAffineLine k))
      (hh : projectiveLineChartInclusion a (fa x) ≠ projectiveLineChartInclusion b (fb x)) :
      detPair (chartVector a (sectionEvaluation V x (affineCoordinateSection fa)))
        (chartVector b (sectionEvaluation V x (affineCoordinateSection fb))) ≠ 0 := by
    apply detPair_ne_zero _ _ (chartVector_ne_zero _ _) (chartVector_ne_zero _ _)
    intro he
    apply hh
    rw [affineCoordinateSection_spec fa x, affineCoordinateSection_spec fb x,
      chartInclusion_affinePoint, chartInclusion_affinePoint]
    apply projectiveLinePointEquiv.injective
    simpa only [projectiveLinePointEquiv_projectivePointOfVector] using he
  rw [localTripleMatrix_evaluation, tripleMatrix_det]
  exact mul_ne_zero (mul_ne_zero (hn i1 i0 f1 f0 (h10 x)) (hn ii i1 fi f1 (hi1 x)))
    (hn ii i0 fi f0 (hi0 x))

private def pgl2OnChartTriple {V : Geometric k} (i0 i1 ii : Fin 2)
    (f0 f1 fi : Morphism V (polynomialAffineLine k))
    (h10 : ∀ x, projectiveLineChartInclusion i1 (f1 x) ≠ projectiveLineChartInclusion i0 (f0 x))
    (hi1 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i1 (f1 x))
    (hi0 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i0 (f0 x)) :
    Morphism V (ofAffine (pgl2Variety (k := k))) :=
  Morphism.comp (matrixOfSections (localTripleMatrix i0 i1 ii f0 f1 fi)
    (chartTriple_det_ne_zero i0 i1 ii f0 f1 fi h10 hi1 hi0))
    (ofAffine_morphism pgl2GeneralLinearProjection.toVariety)

set_option backward.isDefEq.respectTransparency false in
private lemma pgl2OnChartTriple_marked {V : Geometric k} (i0 i1 ii : Fin 2)
    (f0 f1 fi : Morphism V (polynomialAffineLine k))
    (h10 : ∀ x, projectiveLineChartInclusion i1 (f1 x) ≠ projectiveLineChartInclusion i0 (f0 x))
    (hi1 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i1 (f1 x))
    (hi0 : ∀ x, projectiveLineChartInclusion ii (fi x) ≠ projectiveLineChartInclusion i0 (f0 x))
    (x : Point V) :
    let g := affinePointEquiv _ (pgl2OnChartTriple i0 i1 ii f0 f1 fi h10 hi1 hi0 x)
    g • projectiveLineZero (k := k) = projectiveLineChartInclusion i0 (f0 x) ∧
    g • projectiveLineOne (k := k) = projectiveLineChartInclusion i1 (f1 x) ∧
    g • projectiveLineInfinity (k := k) = projectiveLineChartInclusion ii (fi x) := by
  let t0 := sectionEvaluation V x (affineCoordinateSection f0)
  let t1 := sectionEvaluation V x (affineCoordinateSection f1)
  let ti := sectionEvaluation V x (affineCoordinateSection fi)
  let M := Matrix.GeneralLinearGroup.mkOfDetNeZero _
    (chartTriple_det_ne_zero i0 i1 ii f0 f1 fi h10 hi1 hi0 x)
  let g := affinePointEquiv _ (pgl2OnChartTriple i0 i1 ii f0 f1 fi h10 hi1 hi0 x)
  let F := matrixOfSections (localTripleMatrix i0 i1 ii f0 f1 fi)
    (chartTriple_det_ne_zero i0 i1 ii f0 f1 fi h10 hi1 hi0)
  have hg : g = pgl2GeneralLinearProjection.onPoints (affinePointEquiv _ (F x)) := by
    exact (congrArg (affinePointEquiv _) (Morphism.comp_apply_point F
      (ofAffine_morphism pgl2GeneralLinearProjection.toVariety) x)).trans
        (affinePointEquiv_ofAffine_morphism pgl2GeneralLinearProjection.toVariety (F x))
  have hM : Matrix.ProjGenLinGroup.mk M = pgl2PointMulEquiv g := by
    rw [hg, pgl2GeneralLinearProjection_points]
    have hf := matrixOfSections_apply (localTripleMatrix i0 i1 ii f0 f1 fi)
      (chartTriple_det_ne_zero i0 i1 ii f0 f1 fi h10 hi1 hi0) x
    change affinePointEquiv _ (F x) = (glPointEquiv 2).symm M at hf
    rw [hf, Equiv.apply_symm_apply]
  have hval : M.val = tripleMatrix (chartVector i0 t0) (chartVector i1 t1) (chartVector ii ti) :=
    localTripleMatrix_evaluation i0 i1 ii f0 f1 fi x
  have h0 := affineCoordinateSection_spec f0 x
  have h1 := affineCoordinateSection_spec f1 x
  have hi := affineCoordinateSection_spec fi x
  refine ⟨?_, ?_, ?_⟩
  · change g • projectiveLineZero (k := k) = _
    rw [h0, chartInclusion_affinePoint]
    apply projectiveLinePointEquiv.injective
    rw [projectiveLineZero, projectiveLineAffinePoint, pgl2ProjectiveLinePointMulAction_mk g M hM,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    refine ⟨detPair (chartVector ii ti) (chartVector i1 t1), ?_⟩
    rw [hval, tripleMatrix_zero]
  · change g • projectiveLineOne (k := k) = _
    rw [h1, chartInclusion_affinePoint]
    apply projectiveLinePointEquiv.injective
    rw [projectiveLineOne, projectiveLineAffinePoint, pgl2ProjectiveLinePointMulAction_mk g M hM,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    refine ⟨detPair (chartVector ii ti) (chartVector i0 t0), ?_⟩
    rw [hval, tripleMatrix_one]
  · change g • projectiveLineInfinity (k := k) = _
    rw [hi, chartInclusion_affinePoint]
    apply projectiveLinePointEquiv.injective
    rw [projectiveLineInfinity, pgl2ProjectiveLinePointMulAction_mk g M hM,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    refine ⟨detPair (chartVector i1 t1) (chartVector i0 t0), ?_⟩
    rw [hval, tripleMatrix_infinity]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse to the three-point orbit map is regular on every product of
standard affine charts. -/
theorem exists_pgl2_morphism_on_charts {V : Geometric k}
    (f0 f1 fi : Morphism V (projectiveLine k)) (i0 i1 ii : Fin 2)
    (h0 : ∀ x : Point V, (f0 x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k i0)
    (h1 : ∀ x : Point V, (f1 x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k i1)
    (hi : ∀ x : Point V, (fi x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k ii)
    (h10 : ∀ x, f1 x ≠ f0 x) (hi1 : ∀ x, fi x ≠ f1 x) (hi0 : ∀ x, fi x ≠ f0 x) :
    ∃ F : Morphism V (ofAffine (pgl2Variety (k := k))), ∀ x : Point V,
      let g := affinePointEquiv _ (F x)
      g • projectiveLineZero (k := k) = f0 x ∧
      g • projectiveLineOne (k := k) = f1 x ∧
      g • projectiveLineInfinity (k := k) = fi x := by
  let t0 := chartLift i0 f0 h0
  let t1 := chartLift i1 f1 h1
  let ti := chartLift ii fi hi
  have ht10 : ∀ x, projectiveLineChartInclusion i1 (t1 x) ≠ projectiveLineChartInclusion i0 (t0 x) := by
    intro x
    exact fun he => h10 x ((chartLift_apply i1 f1 h1 x).symm.trans
      (he.trans (chartLift_apply i0 f0 h0 x)))
  have hti1 : ∀ x, projectiveLineChartInclusion ii (ti x) ≠ projectiveLineChartInclusion i1 (t1 x) := by
    intro x
    exact fun he => hi1 x ((chartLift_apply ii fi hi x).symm.trans
      (he.trans (chartLift_apply i1 f1 h1 x)))
  have hti0 : ∀ x, projectiveLineChartInclusion ii (ti x) ≠ projectiveLineChartInclusion i0 (t0 x) := by
    intro x
    exact fun he => hi0 x ((chartLift_apply ii fi hi x).symm.trans
      (he.trans (chartLift_apply i0 f0 h0 x)))
  refine ⟨pgl2OnChartTriple i0 i1 ii t0 t1 ti ht10 hti1 hti0, ?_⟩
  intro x
  obtain ⟨ha,hb,hc⟩ := pgl2OnChartTriple_marked i0 i1 ii t0 t1 ti ht10 hti1 hti0 x
  exact ⟨ha.trans (chartLift_apply i0 f0 h0 x), hb.trans (chartLift_apply i1 f1 h1 x),
    hc.trans (chartLift_apply ii fi hi x)⟩

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
