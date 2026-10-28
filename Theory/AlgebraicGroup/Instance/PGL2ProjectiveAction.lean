module

public import Theory.AlgebraicGroup.Bor1.MorphicActionPointStabilizer
public import Theory.AlgebraicGroup.Instance.PGL2ProjectiveActionDescent
public import Theory.AlgebraicGroup.RootSubgroups.SL2RootCurves
public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Variety.ProjectiveLine

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The regular PGL2 action on the geometric projective line

This module packages the standard action of the affine `PGL2` carrier on the
scheme-backed geometric projective line as a genuine `MorphicAction`.  Its
scheme morphism `PGL2 x P1 -> P1` is obtained by fpqc descent of the
projective-linear `SL2` action in `PGL2ProjectiveActionDescent`; the full
scheme-theoretic kernel pair, rather than only its rational points, is used so
the construction remains valid in characteristic two.  The carrier-point
equivalence then identifies its rational-point map with Mathlib's
projectivization action.

`Projectivization.PGL.mk_smul_mk` gives the representative formula and the two
usual Mobius formulas on the affine charts.  The stabilizers of infinity,
zero, and `[1:1]` are packaged as closed subgroups and identified by elementary
matrix equations.  The standard upper and lower `SL2` root curves are projected
regularly into the affine `PGL2` carrier.

These are the homogeneous-coordinate formulas used in Borel, *Linear
Algebraic Groups*, Section 7.2, and in the rank-one discussion around Theorem
6.8.  The projective-line carrier and point equivalence come from
`Theory.AlgebraicGroup.Variety.ProjectiveLine`; the affine quotient bridge comes
from `Theory.AlgebraicGroup.Instance.PGL2`, and regularity comes from faithfully
flat descent along the central projection.
-/

open scoped LinearAlgebra.Projectivization MatrixGroups

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The standard `PGL2` action on rational points of the geometric projective
line, transported through the two canonical point equivalences. -/
@[instance_reducible]
public noncomputable def pgl2ProjectiveLinePointMulAction :
    MulAction (Variety.Point (pgl2Variety (k := k))) (Point (projectiveLine k)) := by
  letI : MulAction (Variety.Point (pgl2Variety (k := k)))
      (Projectivization k (Fin 2 -> k)) :=
    MulAction.compHom _ (pgl2PointMulEquiv (k := k)).toMonoidHom
  exact Equiv.mulAction (Variety.Point (pgl2Variety (k := k)))
    (projectiveLinePointEquiv (k := k))

/-- Under the projective-line point equivalence, the transported point action
is Mathlib's standard `PGL2` action on projectivization. -/
public theorem pgl2ProjectiveLinePointMulAction_equiv
    (g : Variety.Point (pgl2Variety (k := k))) (x : Point (projectiveLine k)) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    projectiveLinePointEquiv (g • x) =
      pgl2PointMulEquiv (k := k) g • projectiveLinePointEquiv x := by
  letI : MulAction (Variety.Point (pgl2Variety (k := k)))
      (Projectivization k (Fin 2 -> k)) :=
    MulAction.compHom _ (pgl2PointMulEquiv (k := k)).toMonoidHom
  change projectiveLinePointEquiv
      ((projectiveLinePointEquiv (k := k)).symm
        (pgl2PointMulEquiv (k := k) g • projectiveLinePointEquiv x)) = _
  exact (projectiveLinePointEquiv (k := k)).apply_symm_apply _

private theorem pgl2RankTwoIndex_eq :
    Fin (Module.finrank k (Fin 2 -> k)) = Fin 2 := by
  exact congrArg Fin (Module.finrank_fin_fun k)

private noncomputable def pgl2ProjectiveStandardBasis :
    Module.Basis (Fin (Module.finrank k (Fin 2 -> k))) k (Fin 2 -> k) :=
  (Pi.basisFun k (Fin 2)).reindex
    (Equiv.cast (pgl2RankTwoIndex_eq (k := k)).symm)

private theorem projectiveSpaceByCoordinates_eq_of_eq
    {sigma tau : Type} [Finite sigma] [Finite tau] (h : sigma = tau) :
    projectiveSpaceByCoordinates k sigma = projectiveSpaceByCoordinates k tau := by
  cases h
  rfl

private theorem projectiveSpaceFinTwo_eq_projectiveLine :
    projectiveSpace k (Fin 2 -> k) = projectiveLine k := by
  change projectiveSpaceByCoordinates k (Fin (Module.finrank k (Fin 2 -> k))) =
    projectiveSpaceByCoordinates k (Fin 2)
  exact projectiveSpaceByCoordinates_eq_of_eq (k := k)
    (pgl2RankTwoIndex_eq (k := k))

private theorem reindexedCoordinatePointEquiv_eq
    {sigma tau : Type} [Finite sigma] [Finite tau]
    (h : sigma = tau) (x : Point (projectiveSpaceByCoordinates k tau)) :
    let b : Module.Basis sigma k (tau -> k) :=
      (Pi.basisFun k tau).reindex (Equiv.cast h.symm)
    let hV : projectiveSpaceByCoordinates k sigma =
        projectiveSpaceByCoordinates k tau :=
      projectiveSpaceByCoordinates_eq_of_eq (k := k) h
    ((projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := sigma)).trans
      (projectivizationEquivOfLinearEquiv b.equivFun.symm)) (hV.symm ▸ x) =
        projectiveSpaceByCoordinatesPointEquiv x := by
  cases h
  simp only [Equiv.trans_apply]
  induction hq : projectiveSpaceByCoordinatesPointEquiv x using Projectivization.ind with
  | h v hv =>
    change Projectivization.map
        ((Pi.basisFun k sigma).reindex (Equiv.cast rfl)).equivFun.symm.toLinearMap
        ((Pi.basisFun k sigma).reindex (Equiv.cast rfl)).equivFun.symm.injective
        (Projectivization.mk k v hv) = Projectivization.mk k v hv
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨1, ?_⟩
    simp [Pi.basisFun_equivFun]

private theorem pgl2ProjectiveStandardBasis_pointEquiv
    (x : Point (projectiveLine k)) :
    ((projectiveSpaceByCoordinatesPointEquiv
        (k := k) (sigma := Fin (Module.finrank k (Fin 2 -> k)))).trans
      (projectivizationEquivOfLinearEquiv
        (pgl2ProjectiveStandardBasis (k := k)).equivFun.symm))
        (show Point (projectiveRankTwo (k := k)) from
          projectiveRankTwo_eq_projectiveLine (k := k) |>.symm ▸ x) =
      projectiveLinePointEquiv x := by
  have he : projectiveSpaceFinTwo_eq_projectiveLine (k := k) =
      projectiveRankTwo_eq_projectiveLine (k := k) := Subsingleton.elim _ _
  rw [← he]
  exact reindexedCoordinatePointEquiv_eq
    (k := k) (pgl2RankTwoIndex_eq (k := k)) x

omit [IsAlgClosed k] in
private theorem castSLProjectiveAction
    {n : Nat} (hn : n = 2) (A : Matrix.SpecialLinearGroup (Fin n) k)
    (q : Projectivization k (Fin n -> k)) :
    let b : Module.Basis (Fin n) k (Fin 2 -> k) :=
      (Pi.basisFun k (Fin 2)).reindex (Equiv.cast (congrArg Fin hn).symm)
    let c : Matrix.ProjGenLinGroup (Fin n) k ≃* PGL2 k := by rw [hn]
    projectivizationEquivOfLinearEquiv b.equivFun.symm
        (Matrix.SpecialLinearGroup.toPGL A • q) =
      c (Matrix.SpecialLinearGroup.toPGL A) •
        projectivizationEquivOfLinearEquiv b.equivFun.symm q := by
  cases hn
  simp [projectivizationEquivOfLinearEquiv, Pi.basisFun_equivFun]

/-- The projective-linear `SL2` action agrees on points with the transported
`PGL2` action after applying the central projection. -/
public theorem sl2ProjectiveLinePointMulAction_projection
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveLine k)) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    (sl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul s x =
      (pgl2Projection (k := k)).onPoints s • x := by
  let b := pgl2ProjectiveStandardBasis (k := k)
  let e := projectiveRankTwo_eq_projectiveLine (k := k)
  let x' : Point (projectiveRankTwo (k := k)) := e.symm ▸ x
  apply (projectiveLinePointEquiv (k := k)).injective
  rw [pgl2ProjectiveLinePointMulAction_equiv,
    pgl2PointMulEquiv_projection]
  rw [← pgl2ProjectiveStandardBasis_pointEquiv (k := k)
    ((sl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul s x)]
  have htransport :
      (show Point (projectiveRankTwo (k := k)) from
        e.symm ▸
          (sl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul s x) =
        (sl2ProjectiveCoordinateMorphicAction (k := k)).toMulAction.smul s x' := by
    simpa only [e, x'] using
      sl2ProjectiveLineMorphicAction_smul_transport (k := k) s x
  rw [htransport]
  change projectivizationEquivOfLinearEquiv b.equivFun.symm
      (projectiveSpaceByCoordinatesPointEquiv
        ((sl2ProjectiveCoordinateMorphicAction (k := k)).toMulAction.smul s x')) = _
  rw [sl2ProjectiveMorphicAction_projectiveSpaceByCoordinatesPointEquiv]
  have hcast :
      projectivizationEquivOfLinearEquiv b.equivFun.symm
          (Matrix.SpecialLinearGroup.toPGL
              (slPointEquiv (Module.finrank k (Fin 2 -> k)) s) •
            projectiveSpaceByCoordinatesPointEquiv x') =
        pgl2SLPointClass s •
          projectivizationEquivOfLinearEquiv b.equivFun.symm
            (projectiveSpaceByCoordinatesPointEquiv x') := by
    simpa only [b, pgl2ProjectiveStandardBasis, pgl2RankTwoIndex_eq,
      pgl2SLPointClass] using
      castSLProjectiveAction (k := k) (Module.finrank_fin_fun k)
        (slPointEquiv (Module.finrank k (Fin 2 -> k)) s)
        (projectiveSpaceByCoordinatesPointEquiv x')
  have hxEquiv :
      projectivizationEquivOfLinearEquiv b.equivFun.symm
          (projectiveSpaceByCoordinatesPointEquiv x') =
        projectiveLinePointEquiv x := by
    simpa only [b, e, x', Equiv.trans_apply] using
      pgl2ProjectiveStandardBasis_pointEquiv (k := k) x
  rw [hcast, hxEquiv]

private theorem pgl2Projection_onPoints_surjective :
    Function.Surjective (pgl2Projection (k := k)).onPoints := by
  exact (pgl2TensorMorphism (k := k)).codRestrictImageClosedSubgroup_surjective
    (fun x => ⟨x, rfl⟩)

/-- The descended scheme morphism induces exactly the standard transported
`PGL2` action on rational points. -/
public theorem pgl2ProjectiveLineActionMorphism_apply
    (g : Variety.Point (pgl2Variety (k := k)))
    (x : Point (projectiveLine k)) :
    pgl2ProjectiveLineActionMorphism (k := k)
        (prodPoint ((affinePointEquiv (pgl2Variety (k := k))).symm g) x) =
      letI := pgl2ProjectiveLinePointMulAction (k := k)
      g • x := by
  obtain ⟨s, rfl⟩ := pgl2Projection_onPoints_surjective (k := k) g
  rw [pgl2ProjectiveLineActionMorphism_projection_apply]
  exact sl2ProjectiveLinePointMulAction_projection (k := k) s x

/-- The genuine regular action of the affine `PGL2` carrier on geometric
projective one-space. -/
@[expose] public noncomputable def pgl2ProjectiveLineMorphicAction :
    MorphicAction (pgl2Variety (k := k)) (projectiveLine k) where
  toMulAction := pgl2ProjectiveLinePointMulAction (k := k)
  actionMorphism := pgl2ProjectiveLineActionMorphism (k := k)
  actionMorphism_apply := pgl2ProjectiveLineActionMorphism_apply (k := k)

/-- An invertible two-dimensional matrix sends a nonzero vector to a nonzero
vector. -/
public lemma gl2_mulVec_ne_zero (A : GL (Fin 2) k)
    (v : Fin 2 -> k) (hv : v ≠ 0) : A.1.mulVec v ≠ 0 := by
  change A • v ≠ 0
  exact (smul_ne_zero_iff_ne A).2 hv

/-- The action of a `PGL2` point represented by an invertible matrix is the
projective class of the matrix-vector product. -/
public theorem pgl2ProjectiveLinePointMulAction_mk
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g)
    (v : Fin 2 -> k) (hv : v ≠ 0) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    projectiveLinePointEquiv
        (g • projectivePointOfVector v hv) =
      Projectivization.mk k (A.1.mulVec v)
        (gl2_mulVec_ne_zero A v hv) := by
  rw [pgl2ProjectiveLinePointMulAction_equiv,
    projectiveLinePointEquiv_projectivePointOfVector, hA.symm,
    Projectivization.PGL.mk_smul_mk]
  rfl

/-- Homogeneous coordinates `[t:1]` for the standard affine chart. -/
public def projectiveLineAffineVector (t : k) : Fin 2 -> k := ![t, 1]

/-- Homogeneous coordinates `[1:0]` for infinity. -/
public def projectiveLineInfinityVector : Fin 2 -> k := ![1, 0]

/-- Homogeneous coordinates `[1:t]` for the chart around infinity. -/
public def projectiveLineInfinityChartVector (t : k) : Fin 2 -> k := ![1, t]

private lemma projectiveLineAffineVector_ne_zero (t : k) :
    projectiveLineAffineVector t ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [projectiveLineAffineVector] at h1

private lemma projectiveLineInfinityVector_ne_zero :
    (projectiveLineInfinityVector : Fin 2 -> k) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [projectiveLineInfinityVector] at h0

private lemma projectiveLineInfinityChartVector_ne_zero (t : k) :
    projectiveLineInfinityChartVector t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [projectiveLineInfinityChartVector] at h0

/-- The rational point `[t:1]` on the standard affine chart. -/
public noncomputable def projectiveLineAffinePoint (t : k) : Point (projectiveLine k) :=
  projectivePointOfVector (projectiveLineAffineVector t)
    (projectiveLineAffineVector_ne_zero t)

/-- The rational point at infinity, with homogeneous coordinates `[1:0]`. -/
public noncomputable def projectiveLineInfinity : Point (projectiveLine k) :=
  projectivePointOfVector projectiveLineInfinityVector
    projectiveLineInfinityVector_ne_zero

/-- The rational point `[1:t]` on the affine chart around infinity. -/
public noncomputable def projectiveLineInfinityChartPoint (t : k) :
    Point (projectiveLine k) :=
  projectivePointOfVector (projectiveLineInfinityChartVector t)
    (projectiveLineInfinityChartVector_ne_zero t)

/-- The point zero, with homogeneous coordinates `[0:1]`. -/
public noncomputable def projectiveLineZero : Point (projectiveLine k) :=
  projectiveLineAffinePoint 0

/-- The point one, with homogeneous coordinates `[1:1]`. -/
public noncomputable def projectiveLineOne : Point (projectiveLine k) :=
  projectiveLineAffinePoint 1

private lemma gl2_mulVec_affineVector (A : GL (Fin 2) k) (t : k) :
    A.1.mulVec (projectiveLineAffineVector t) =
      ![A.1 0 0 * t + A.1 0 1, A.1 1 0 * t + A.1 1 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, projectiveLineAffineVector, Fin.sum_univ_two]

private lemma gl2_mulVec_infinityChartVector (A : GL (Fin 2) k) (t : k) :
    A.1.mulVec (projectiveLineInfinityChartVector t) =
      ![A.1 0 0 + A.1 0 1 * t, A.1 1 0 + A.1 1 1 * t] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, projectiveLineInfinityChartVector,
      Fin.sum_univ_two]

/-- The homogeneous numerator-denominator vector for the Mobius action on
the standard affine chart. -/
public def pgl2MobiusVector (A : GL (Fin 2) k) (t : k) : Fin 2 -> k :=
  ![A.1 0 0 * t + A.1 0 1, A.1 1 0 * t + A.1 1 1]

/-- The homogeneous Mobius numerator-denominator vector is nonzero. -/
public lemma pgl2MobiusVector_ne_zero (A : GL (Fin 2) k) (t : k) :
    pgl2MobiusVector A t ≠ 0 := by
  change ![A.1 0 0 * t + A.1 0 1, A.1 1 0 * t + A.1 1 1] ≠ 0
  rw [← gl2_mulVec_affineVector]
  exact gl2_mulVec_ne_zero A (projectiveLineAffineVector t)
    (projectiveLineAffineVector_ne_zero t)

/-- Homogeneous form of the `PGL2` action on the standard affine chart. -/
public theorem pgl2ProjectiveLinePointMulAction_affine
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g)
    (t : k) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    projectiveLinePointEquiv (g • projectiveLineAffinePoint t) =
      Projectivization.mk k (pgl2MobiusVector A t)
        (pgl2MobiusVector_ne_zero A t) := by
  have h := pgl2ProjectiveLinePointMulAction_mk
    (k := k) g A hA (projectiveLineAffineVector t)
      (projectiveLineAffineVector_ne_zero t)
  rw [projectiveLineAffinePoint]
  rw [h]
  congr 1
  exact gl2_mulVec_affineVector A t

/-- On the standard affine chart, a representative matrix
`[[a,b],[c,d]]` acts by `t |-> (a*t+b)/(c*t+d)` whenever the denominator is
nonzero. -/
public theorem pgl2ProjectiveLinePointMulAction_affine_chart
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g)
    (t : k) (hden : A.1 1 0 * t + A.1 1 1 ≠ 0) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    g • projectiveLineAffinePoint t =
      projectiveLineAffinePoint ((A.1 0 0 * t + A.1 0 1) /
        (A.1 1 0 * t + A.1 1 1)) := by
  apply (projectiveLinePointEquiv (k := k)).injective
  rw [pgl2ProjectiveLinePointMulAction_affine (k := k) g A hA t]
  rw [projectiveLineAffinePoint, projectiveLinePointEquiv_projectivePointOfVector]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
  refine ⟨A.1 1 0 * t + A.1 1 1, ?_⟩
  funext i
  fin_cases i
  · change (A.1 1 0 * t + A.1 1 1) *
        ((A.1 0 0 * t + A.1 0 1) / (A.1 1 0 * t + A.1 1 1)) =
      A.1 0 0 * t + A.1 0 1
    exact mul_div_cancel₀ _ hden
  · simp [projectiveLineAffineVector, pgl2MobiusVector]

/-- On the chart `[1:t]` around infinity, a representative matrix
`[[a,b],[c,d]]` acts by `t |-> (c+d*t)/(a+b*t)` whenever the denominator is
nonzero. -/
public theorem pgl2ProjectiveLinePointMulAction_infinity_chart
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g)
    (t : k) (hnum : A.1 0 0 + A.1 0 1 * t ≠ 0) :
    letI := pgl2ProjectiveLinePointMulAction (k := k)
    g • projectiveLineInfinityChartPoint t =
      projectiveLineInfinityChartPoint ((A.1 1 0 + A.1 1 1 * t) /
        (A.1 0 0 + A.1 0 1 * t)) := by
  apply (projectiveLinePointEquiv (k := k)).injective
  have h := pgl2ProjectiveLinePointMulAction_mk
    (k := k) g A hA (projectiveLineInfinityChartVector t)
      (projectiveLineInfinityChartVector_ne_zero t)
  rw [projectiveLineInfinityChartPoint]
  rw [h]
  simp only [projectiveLineInfinityChartPoint,
    projectiveLinePointEquiv_projectivePointOfVector]
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
  refine ⟨A.1 0 0 + A.1 0 1 * t, ?_⟩
  rw [gl2_mulVec_infinityChartVector]
  funext i
  fin_cases i
  · simp [projectiveLineInfinityChartVector]
  · change (A.1 0 0 + A.1 0 1 * t) *
        ((A.1 1 0 + A.1 1 1 * t) / (A.1 0 0 + A.1 0 1 * t)) =
      A.1 1 0 + A.1 1 1 * t
    exact mul_div_cancel₀ _ hnum

/-- The point stabilizer of infinity. -/
public noncomputable abbrev pgl2InfinityStabilizer :
    Subgroup (Variety.Point (pgl2Variety (k := k))) := by
  letI := pgl2ProjectiveLinePointMulAction (k := k)
  exact MulAction.stabilizer _ (projectiveLineInfinity (k := k))

/-- The point stabilizer of zero. -/
public noncomputable abbrev pgl2ZeroStabilizer :
    Subgroup (Variety.Point (pgl2Variety (k := k))) := by
  letI := pgl2ProjectiveLinePointMulAction (k := k)
  exact MulAction.stabilizer _ (projectiveLineZero (k := k))

/-- The point stabilizer of `[1:1]`. -/
public noncomputable abbrev pgl2OneStabilizer :
    Subgroup (Variety.Point (pgl2Variety (k := k))) := by
  letI := pgl2ProjectiveLinePointMulAction (k := k)
  exact MulAction.stabilizer _ (projectiveLineOne (k := k))

/-- The closed stabilizer of infinity for the regular `PGL2` action. -/
public noncomputable def pgl2InfinityStabilizerClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer
    (projectiveLineInfinity (k := k))

/-- The closed stabilizer of zero for the regular `PGL2` action. -/
public noncomputable def pgl2ZeroStabilizerClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer
    (projectiveLineZero (k := k))

/-- The closed stabilizer of `[1:1]` for the regular `PGL2` action. -/
public noncomputable def pgl2OneStabilizerClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer
    (projectiveLineOne (k := k))

@[simp]
public theorem pgl2InfinityStabilizerClosed_toSubgroup :
    (pgl2InfinityStabilizerClosed (k := k)).toSubgroup =
      pgl2InfinityStabilizer (k := k) := by
  exact (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer_toSubgroup
    (projectiveLineInfinity (k := k))

@[simp]
public theorem pgl2ZeroStabilizerClosed_toSubgroup :
    (pgl2ZeroStabilizerClosed (k := k)).toSubgroup =
      pgl2ZeroStabilizer (k := k) := by
  exact (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer_toSubgroup
    (projectiveLineZero (k := k))

@[simp]
public theorem pgl2OneStabilizerClosed_toSubgroup :
    (pgl2OneStabilizerClosed (k := k)).toSubgroup =
      pgl2OneStabilizer (k := k) := by
  exact (pgl2ProjectiveLineMorphicAction (k := k)).pointStabilizer_toSubgroup
    (projectiveLineOne (k := k))

/-- The standard upper Borel point subgroup, defined as the stabilizer of
infinity. -/
public noncomputable abbrev pgl2UpperBorel :
    Subgroup (Variety.Point (pgl2Variety (k := k))) :=
  pgl2InfinityStabilizer (k := k)

/-- The standard lower Borel point subgroup, defined as the stabilizer of
zero. -/
public noncomputable abbrev pgl2LowerBorel :
    Subgroup (Variety.Point (pgl2Variety (k := k))) :=
  pgl2ZeroStabilizer (k := k)

/-- The standard upper Borel as a closed subgroup of the affine `PGL2`
carrier. -/
public noncomputable abbrev pgl2UpperBorelClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  pgl2InfinityStabilizerClosed (k := k)

/-- The standard lower Borel as a closed subgroup of the affine `PGL2`
carrier. -/
public noncomputable abbrev pgl2LowerBorelClosed :
    ClosedSubgroup (pgl2Variety (k := k)) :=
  pgl2ZeroStabilizerClosed (k := k)

/-- A matrix representative fixes infinity exactly when its lower-left entry
vanishes; thus this stabilizer is the standard upper Borel on points. -/
public theorem mem_pgl2InfinityStabilizer_iff
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g) :
    g ∈ pgl2InfinityStabilizer (k := k) ↔ A.1 1 0 = 0 := by
  change (letI := pgl2ProjectiveLinePointMulAction (k := k)
    g • projectiveLineInfinity (k := k) = projectiveLineInfinity (k := k)) ↔ _
  constructor
  · intro h
    have hp := congrArg (projectiveLinePointEquiv (k := k)) h
    rw [projectiveLineInfinity,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector] at hp
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).1 hp
    have h1 := congrFun ha 1
    simpa [projectiveLineInfinityVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h1.symm
  · intro h10
    apply (projectiveLinePointEquiv (k := k)).injective
    rw [projectiveLineInfinity,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
    refine ⟨A.1 0 0, ?_⟩
    funext i
    fin_cases i <;>
      simp [projectiveLineInfinityVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, h10]

/-- A matrix representative fixes zero exactly when its upper-right entry
vanishes; thus this stabilizer is the standard lower Borel on points. -/
public theorem mem_pgl2ZeroStabilizer_iff
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g) :
    g ∈ pgl2ZeroStabilizer (k := k) ↔ A.1 0 1 = 0 := by
  change (letI := pgl2ProjectiveLinePointMulAction (k := k)
    g • projectiveLineZero (k := k) = projectiveLineZero (k := k)) ↔ _
  rw [projectiveLineZero]
  constructor
  · intro h
    have hp := congrArg (projectiveLinePointEquiv (k := k)) h
    rw [projectiveLineAffinePoint,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector] at hp
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).1 hp
    have h0 := congrFun ha 0
    simpa [projectiveLineAffineVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using h0.symm
  · intro h01
    apply (projectiveLinePointEquiv (k := k)).injective
    rw [projectiveLineAffinePoint,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
    refine ⟨A.1 1 1, ?_⟩
    funext i
    fin_cases i <;>
      simp [projectiveLineAffineVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, h01]

/-- A matrix representative fixes `[1:1]` exactly when its two row sums are
equal. -/
public theorem mem_pgl2OneStabilizer_iff
    (g : Variety.Point (pgl2Variety (k := k))) (A : GL (Fin 2) k)
    (hA : Matrix.ProjGenLinGroup.mk A = pgl2PointMulEquiv (k := k) g) :
    g ∈ pgl2OneStabilizer (k := k) ↔
      A.1 0 0 + A.1 0 1 = A.1 1 0 + A.1 1 1 := by
  change (letI := pgl2ProjectiveLinePointMulAction (k := k)
    g • projectiveLineOne (k := k) = projectiveLineOne (k := k)) ↔ _
  rw [projectiveLineOne]
  constructor
  · intro h
    have hp := congrArg (projectiveLinePointEquiv (k := k)) h
    rw [projectiveLineAffinePoint,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector] at hp
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).1 hp
    have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp [projectiveLineAffineVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h0 h1
    exact h0.symm.trans h1
  · intro hsums
    apply (projectiveLinePointEquiv (k := k)).injective
    rw [projectiveLineAffinePoint,
      pgl2ProjectiveLinePointMulAction_mk (k := k) g A hA,
      projectiveLinePointEquiv_projectivePointOfVector]
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).2
    refine ⟨A.1 0 0 + A.1 0 1, ?_⟩
    funext i
    fin_cases i <;>
      simp [projectiveLineAffineVector, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hsums]

/-- The regular upper unipotent curve in the affine `PGL2` carrier. -/
@[expose]
public noncomputable def pgl2UpperUnipotentMorphism :
    AlgebraicGroup.Morphism (KPlus k) (pgl2Variety (k := k)) := by
  let pi := pgl2Projection (k := k)
  rw [Module.finrank_fin_fun k] at pi
  exact pi.comp (standardSL2UpperMorphism (k := k))

/-- The regular lower unipotent curve in the affine `PGL2` carrier. -/
@[expose]
public noncomputable def pgl2LowerUnipotentMorphism :
    AlgebraicGroup.Morphism (KPlus k) (pgl2Variety (k := k)) := by
  let pi := pgl2Projection (k := k)
  rw [Module.finrank_fin_fun k] at pi
  exact pi.comp (standardSL2LowerMorphism (k := k))

end Theory.AlgebraicGroup.Variety.Geometric
