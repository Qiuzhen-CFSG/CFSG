module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Variety.Zariski

/-!
# The closed special-orthogonal carrier

Fixing a basis of a finite-dimensional vector space identifies its general
linear group with `glVarietyOf`.  This module cuts out the quadratic isometries
by the degree-two equations `Q (g v) = Q v`, written using the
characteristic-free bilinear representative `Q.toBilin`.  Intersecting this
zero locus with the generic determinant-one equation gives a genuine
`ClosedSubgroup`, whose rational points are multiplicatively equivalent to
`specialOrthogonalPointGroup Q`.

The construction is the affine-matrix realization required by the standard
odd orthogonal model in GLS3, Theorem 1.10.7(b).  Closedness itself does not
need nondegeneracy, odd dimension, or the characteristic-not-two hypothesis;
those enter the surrounding `OddOrthogonalModel` through its Spin action.  In
particular, this module respects the explicit `[Invertible (2 : k)]` contract
there without introducing it into this characteristic-free carrier result.

The proof first identifies the quadratic stabilizer and determinant-one
subgroups with polynomial zero loci.  Their intersection is packaged as a
closed subgroup, and the basis-transported GL point equivalence is then
restricted to its exact point subgroup.
-/

universe u

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private noncomputable def linearPointMulEquivOf
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (glVarietyOf k V) ≃* (V ≃ₗ[k] V) :=
  ((((translationGLPointMulEquiv (k := k) (Module.finrank k V)).trans
    Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k V))

private noncomputable def glEntryCoordinate
    (i j : Fin (Module.finrank k V)) : (glVarietyOf k V).Coordinates :=
  Sum.inl (i, j)

private noncomputable def glMatrixOfPointOf
    (x : Variety.Point (glVarietyOf k V)) :
    Matrix (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k :=
  fun i j => x.val (glEntryCoordinate (k := k) (V := V) i j)

private lemma glPointEquivOf_apply_basis'
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) (j : Fin (Module.finrank k V)) :
    (glPointEquivOf k V e x).1 (e j) =
      e.equivFun.symm (fun l => glMatrixOfPointOf x l j) := by
  simpa [glMatrixOfPointOf, glEntryCoordinate, glVarietyOf, glMatrixOfPoint] using
    glPointEquivOf_apply_basis V e x j

private noncomputable def transformedCoordinatePolynomial
    (c : Fin (Module.finrank k V) → k) (i : Fin (Module.finrank k V)) :
    MvPolynomial (glVarietyOf k V).Coordinates k :=
  ∑ j, MvPolynomial.C (c j) *
    MvPolynomial.X (glEntryCoordinate (k := k) (V := V) i j)

private noncomputable def quadraticPreservationPolynomial
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (c : Fin (Module.finrank k V) → k) :
    MvPolynomial (glVarietyOf k V).Coordinates k :=
  (∑ i, ∑ j,
      MvPolynomial.C
          (Q.toBilin e (e i) (e j)) *
        transformedCoordinatePolynomial c i * transformedCoordinatePolynomial c j) -
    MvPolynomial.C (Q (e.equivFun.symm c))

omit [FiniteDimensional k V] in
private lemma eval_transformedCoordinatePolynomial
    (c : Fin (Module.finrank k V) → k) (i : Fin (Module.finrank k V))
    (x : Variety.Point (glVarietyOf k V)) :
    evalPolynomial x.val (transformedCoordinatePolynomial c i) =
      (glMatrixOfPointOf x).mulVec c i := by
  rw [transformedCoordinatePolynomial, evalPolynomial_sum]
  simp [evalPolynomial, Matrix.mulVec, dotProduct, glMatrixOfPointOf, mul_comm]

private lemma linearPointMulEquivOf_apply
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (c : Fin (Module.finrank k V) → k)
    (x : Variety.Point (glVarietyOf k V)) :
    linearPointMulEquivOf e x (e.equivFun.symm c) =
      e.equivFun.symm ((glMatrixOfPointOf x).mulVec c) := by
  change (glPointEquivOf k V e x).1 (e.equivFun.symm c) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [map_sum, map_smul, glPointEquivOf_apply_basis']
  apply e.equivFun.injective
  rw [e.equivFun.apply_symm_apply]
  simp only [map_sum, map_smul, e.equivFun.apply_symm_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

private lemma eval_quadraticPreservationPolynomial
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (c : Fin (Module.finrank k V) → k)
    (x : Variety.Point (glVarietyOf k V)) :
    evalPolynomial x.val (quadraticPreservationPolynomial Q e c) =
      Q (linearPointMulEquivOf e x (e.equivFun.symm c)) -
        Q (e.equivFun.symm c) := by
  let B := Q.toBilin e
  let y := linearPointMulEquivOf e x (e.equivFun.symm c)
  have hy (i : Fin (Module.finrank k V)) :
      e.repr y i = (glMatrixOfPointOf x).mulVec c i := by
    dsimp [y]
    rw [linearPointMulEquivOf_apply]
    exact congrFun (e.equivFun.apply_symm_apply _) i
  have hquad : B y y = Q y := by
    calc
      B y y = B.toQuadraticMap y := rfl
      _ = Q y := by rw [QuadraticMap.toQuadraticMap_toBilin Q e]
  have eval_sub (p q : MvPolynomial (glVarietyOf k V).Coordinates k) :
      evalPolynomial x.val (p - q) =
        evalPolynomial x.val p - evalPolynomial x.val q := by
    simp [evalPolynomial]
  rw [quadraticPreservationPolynomial]
  rw [eval_sub, evalPolynomial_sum]
  simp_rw [evalPolynomial_sum]
  simp_rw [evalPolynomial_mul]
  simp_rw [eval_transformedCoordinatePolynomial]
  simp only [evalPolynomial, MvPolynomial.eval₂_C, RingHom.id_apply]
  rw [← hquad, ← Matrix.toBilin_toMatrix e B,
    Matrix.toBilin_apply]
  simp_rw [LinearMap.BilinForm.toMatrix_apply]
  dsimp [B]
  simp_rw [hy]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

private noncomputable def quadraticIsometryGLSubgroup
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Subgroup (Variety.Point (glVarietyOf k V)) :=
  (quadraticIsometrySubgroup Q).comap (linearPointMulEquivOf e).toMonoidHom

private lemma quadraticIsometryGLSubgroup_isZariskiClosed
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    IsZariskiClosed (glVarietyOf k V)
      (quadraticIsometryGLSubgroup Q e :
        Set (Variety.Point (glVarietyOf k V))) := by
  refine ⟨{p | ∃ c, p = quadraticPreservationPolynomial Q e c}, ?_⟩
  ext x
  constructor
  · intro hx p hp
    obtain ⟨c, rfl⟩ := hp
    rw [eval_quadraticPreservationPolynomial]
    change linearPointMulEquivOf e x ∈ quadraticIsometrySubgroup Q at hx
    rw [mem_quadraticIsometrySubgroup] at hx
    exact sub_eq_zero.mpr (hx (e.equivFun.symm c))
  · intro hx
    change linearPointMulEquivOf e x ∈ quadraticIsometrySubgroup Q
    rw [mem_quadraticIsometrySubgroup]
    intro v
    let c := e.equivFun v
    have h := hx (quadraticPreservationPolynomial Q e c) ⟨c, rfl⟩
    rw [eval_quadraticPreservationPolynomial] at h
    simpa [c] using sub_eq_zero.mp h

private noncomputable def determinantOnePolynomial :
    MvPolynomial (glVarietyOf k V).Coordinates k :=
  MvPolynomial.rename
      (fun ij => glEntryCoordinate (k := k) (V := V) ij.1 ij.2)
      (glDetPolynomial (k := k) (Module.finrank k V)) - 1

omit [FiniteDimensional k V] in
private lemma eval_determinantOnePolynomial
    (x : Variety.Point (glVarietyOf k V)) :
    evalPolynomial x.val (determinantOnePolynomial (k := k) (V := V)) =
      (glMatrixOfPointOf x).det - 1 := by
  have hdet : evalPolynomial x.val
      (MvPolynomial.rename
        (fun ij => glEntryCoordinate (k := k) (V := V) ij.1 ij.2)
        (glDetPolynomial (k := k) (Module.finrank k V))) =
      (glMatrixOfPointOf x).det := by
    rw [evalPolynomial_rename, evalPolynomial]
    rw [glDetPolynomial]
    change MvPolynomial.eval
      (x.val ∘ fun ij => glEntryCoordinate (k := k) (V := V) ij.1 ij.2)
      (Matrix.det (Matrix.mvPolynomialX
        (Fin (Module.finrank k V)) (Fin (Module.finrank k V)) k)) =
        (glMatrixOfPointOf x).det
    rw [Matrix.eval_det_mvPolynomialX]
    rfl
  rw [determinantOnePolynomial]
  simpa [evalPolynomial, hdet]

private lemma glMatrixOfPointOf_eq_toMatrix
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) :
    glMatrixOfPointOf x =
      LinearMap.toMatrix e e
        ((linearPointMulEquivOf e x : V ≃ₗ[k] V) : Module.End k V) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change x.val (glEntryCoordinate (k := k) (V := V) i j) =
    e.repr ((glPointEquivOf k V e x).1 (e j)) i
  rw [glPointEquivOf_apply_basis']
  change x.val (glEntryCoordinate (k := k) (V := V) i j) =
    e.equivFun (e.equivFun.symm
      (fun l => glMatrixOfPointOf x l j)) i
  rw [e.equivFun.apply_symm_apply]
  rfl

private noncomputable def determinantOneGLSubgroup
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Subgroup (Variety.Point (glVarietyOf k V)) :=
  LinearEquiv.det.ker.comap (linearPointMulEquivOf e).toMonoidHom

private lemma determinantOneGLSubgroup_isZariskiClosed
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    IsZariskiClosed (glVarietyOf k V)
      (determinantOneGLSubgroup e :
        Set (Variety.Point (glVarietyOf k V))) := by
  refine ⟨{determinantOnePolynomial (k := k) (V := V)}, ?_⟩
  ext x
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hx p hp
    subst p
    rw [eval_determinantOnePolynomial, sub_eq_zero]
    rw [glMatrixOfPointOf_eq_toMatrix e x, LinearMap.det_toMatrix]
    change LinearEquiv.det (linearPointMulEquivOf e x) = 1 at hx
    have h := congrArg Units.val hx
    simpa [LinearEquiv.coe_det] using h
  · intro hx
    have h := hx (determinantOnePolynomial (k := k) (V := V)) (Set.mem_singleton _)
    rw [eval_determinantOnePolynomial, sub_eq_zero,
      glMatrixOfPointOf_eq_toMatrix e x, LinearMap.det_toMatrix] at h
    change LinearEquiv.det (linearPointMulEquivOf e x) = 1
    apply Units.ext
    simpa [LinearEquiv.coe_det] using h

private noncomputable def specialOrthogonalGLSubgroup
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    Subgroup (Variety.Point (glVarietyOf k V)) :=
  (specialOrthogonalPointGroup Q).comap (linearPointMulEquivOf e).toMonoidHom

private lemma specialOrthogonalGLSubgroup_isZariskiClosed
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    IsZariskiClosed (glVarietyOf k V)
      (specialOrthogonalGLSubgroup Q e :
        Set (Variety.Point (glVarietyOf k V))) := by
  have hset : (specialOrthogonalGLSubgroup Q e :
      Set (Variety.Point (glVarietyOf k V))) =
      (quadraticIsometryGLSubgroup Q e : Set _) ∩
        (determinantOneGLSubgroup e : Set _) := by
    ext x
    rw [Set.mem_inter_iff]
    change linearPointMulEquivOf e x ∈ specialOrthogonalPointGroup Q ↔ _
    rw [mem_specialOrthogonalPointGroup]
    change ((∀ v, Q (linearPointMulEquivOf e x v) = Q v) ∧
      LinearEquiv.det (linearPointMulEquivOf e x) = 1) ↔
      (linearPointMulEquivOf e x ∈ quadraticIsometrySubgroup Q ∧
        LinearEquiv.det (linearPointMulEquivOf e x) = 1)
    rw [mem_quadraticIsometrySubgroup]
  rw [hset]
  exact isZariskiClosed_inter
    (quadraticIsometryGLSubgroup_isZariskiClosed Q e)
    (determinantOneGLSubgroup_isZariskiClosed e)

/-- The closed subgroup of `GL(V)` preserving `Q` with determinant one, in the
coordinates supplied by `e`. -/
public noncomputable def oddSpecialOrthogonalClosedSubgroup
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    ClosedSubgroup (glVarietyOf k V) :=
  ClosedSubgroup.ofSubgroup (specialOrthogonalGLSubgroup Q e)
    (specialOrthogonalGLSubgroup_isZariskiClosed Q e)

/-- Exact membership in the closed special-orthogonal carrier. -/
public theorem oddSpecialOrthogonalClosedSubgroup_carrier
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : Variety.Point (glVarietyOf k V)) :
    g ∈ (oddSpecialOrthogonalClosedSubgroup Q e).toSubgroup ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V e g) ∈ specialOrthogonalPointGroup Q := by
  rfl

/-- The rational points of the closed carrier are exactly the abstract
special-orthogonal point group. -/
public noncomputable def oddSpecialOrthogonalClosedSubgroupPoints
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    let H := oddSpecialOrthogonalClosedSubgroup Q e
    letI := H.carrierAlgebraicGroup
    Variety.Point H.carrierVariety ≃* specialOrthogonalPointGroup Q := by
  let H := oddSpecialOrthogonalClosedSubgroup Q e
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  let restrictEquiv : H.toSubgroup ≃* specialOrthogonalPointGroup Q :=
    { toFun := fun x => ⟨linearPointMulEquivOf e x.1, x.2⟩
      invFun := fun y => ⟨(linearPointMulEquivOf e).symm y.1, by
        change linearPointMulEquivOf e ((linearPointMulEquivOf e).symm y.1) ∈
          specialOrthogonalPointGroup Q
        rw [(linearPointMulEquivOf e).apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => Subtype.ext ((linearPointMulEquivOf e).symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext ((linearPointMulEquivOf e).apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext ((linearPointMulEquivOf e).map_mul x.1 y.1) }
  exact pointEquiv.trans restrictEquiv

/-- Under the point-group equivalence, a carrier point has the same underlying
linear equivalence as its ambient `GL(V)` image. -/
public theorem oddSpecialOrthogonalClosedSubgroup_linear_points
    (Q : QuadraticForm k V)
    (e : Module.Basis (Fin (Module.finrank k V)) k V) :
    let H := oddSpecialOrthogonalClosedSubgroup Q e
    letI := H.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k V
          (glPointEquivOf k V e (H.inclusion.onPoints x)) =
        (oddSpecialOrthogonalClosedSubgroupPoints Q e x).1 := by
  dsimp only
  intro x
  rfl

end Theory.AlgebraicGroup
