module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.ClassicalPointGroups
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Variety.Zariski

/-!
# The standard symplectic carrier

This module develops the polynomial equations for the standard form on
two copies of `Fin m → k`.  It records the finite-rank and form facts, the
closed point subgroup, and the matrix interpretation through `Matrix.J`.
-/

universe u v

open scoped BigOperators

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

public abbrev symplecticStandardIndex (m : ℕ) := Fin m ⊕ Fin m
public abbrev symplecticStandardSpace (m : ℕ) := symplecticStandardIndex m → k

public noncomputable def symplecticStandardIndexEquiv (m : ℕ) :
    symplecticStandardIndex m ≃ Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) := by
  let hdim : Module.finrank k (symplecticStandardSpace (k := k) m) = 2 * m := by
    simp [symplecticStandardSpace, symplecticStandardIndex,
      Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
    omega
  exact finSumFinEquiv.trans (finCongr (by omega))

public noncomputable def symplecticStandardBasis (m : ℕ) :
    Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m) :=
  (Pi.basisFun k (symplecticStandardIndex m)).reindex (symplecticStandardIndexEquiv (k := k) m)

omit [IsAlgClosed k] in
public lemma symplecticStandardSpace_finrank (m : ℕ) :
    Module.finrank k (symplecticStandardSpace (k := k) m) = 2 * m := by
  simp [symplecticStandardSpace, symplecticStandardIndex,
    Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  omega

omit [IsAlgClosed k] in
public lemma symplecticStandardBasis_apply (m : ℕ) (s : symplecticStandardIndex m) :
    symplecticStandardBasis (k := k) m (symplecticStandardIndexEquiv (k := k) m s) =
      Pi.single s 1 := by
  classical
  simp [symplecticStandardBasis, symplecticStandardIndexEquiv, symplecticStandardIndex]

omit [IsAlgClosed k] in
public lemma symplecticStandardBasis_repr_apply (m : ℕ)
    (x : symplecticStandardSpace (k := k) m) (s : symplecticStandardIndex m) :
    (symplecticStandardBasis (k := k) m).repr x
        (symplecticStandardIndexEquiv (k := k) m s) = x s := by
  classical
  change ((Pi.basisFun k (symplecticStandardIndex m)).reindex
      (symplecticStandardIndexEquiv (k := k) m)).repr x
      (symplecticStandardIndexEquiv (k := k) m s) = x s
  rw [Module.Basis.repr_reindex_apply]
  simp [symplecticStandardIndexEquiv, Pi.basisFun_repr]

omit [IsAlgClosed k] in
public lemma symplecticStandardForm_isAlt (m : ℕ) :
    (Matrix.toBilin' (Matrix.J (Fin m) k) :
      LinearMap.BilinForm k (symplecticStandardSpace (k := k) m)).IsAlt := by
  intro x
  rw [Matrix.toBilin'_apply]
  simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply]
  have hsum : (∑ i : Fin m, x (Sum.inl i) * x (Sum.inr i)) =
      ∑ i : Fin m, x (Sum.inr i) * x (Sum.inl i) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hsum]
  ring

omit [IsAlgClosed k] in
public lemma symplecticStandardForm_nondegenerate (m : ℕ) :
    (Matrix.toBilin' (Matrix.J (Fin m) k) :
      LinearMap.BilinForm k (symplecticStandardSpace (k := k) m)).Nondegenerate := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
  exact (Matrix.isUnit_det_J (Fin m) k).ne_zero

private noncomputable def symplecticLinearPointMulEquivOf
    {m : ℕ}
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)) ≃*
      ((symplecticStandardSpace (k := k) m) ≃ₗ[k]
        (symplecticStandardSpace (k := k) m)) :=
  ((((translationGLPointMulEquiv (k := k)
      (Module.finrank k (symplecticStandardSpace (k := k) m))).trans
    Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)))

private noncomputable def symplecticGlEntryCoordinate
    {m : ℕ}
    (i j : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
    (glVarietyOf k (symplecticStandardSpace (k := k) m)).Coordinates :=
  Sum.inl (i, j)

private noncomputable def symplecticGlMatrixOfPoint
    {m : ℕ}
    (x : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    Matrix (Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
      (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k :=
  fun i j => x.val (symplecticGlEntryCoordinate (k := k) i j)

private lemma symplecticGlPointEquivOf_apply_basis
    {m : ℕ}
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m))
    (x : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)))
    (j : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
    (glPointEquivOf k (symplecticStandardSpace (k := k) m) e x).1 (e j) =
      e.equivFun.symm (fun l => symplecticGlMatrixOfPoint (k := k) x l j) := by
  simpa [symplecticGlMatrixOfPoint, symplecticGlEntryCoordinate, glVarietyOf,
    glMatrixOfPoint] using
    glPointEquivOf_apply_basis (symplecticStandardSpace (k := k) m) e x j

private noncomputable def symplecticTransformedCoordinatePolynomial
    {m : ℕ}
    (c : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (i : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
    MvPolynomial (glVarietyOf k (symplecticStandardSpace (k := k) m)).Coordinates k :=
  ∑ j, MvPolynomial.C (c j) *
    MvPolynomial.X (symplecticGlEntryCoordinate (k := k) i j)

private lemma eval_symplecticTransformedCoordinatePolynomial
    {m : ℕ}
    (c : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (i : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)))
    (x : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    evalPolynomial x.val (symplecticTransformedCoordinatePolynomial (k := k) c i) =
      (symplecticGlMatrixOfPoint (k := k) x).mulVec c i := by
  rw [symplecticTransformedCoordinatePolynomial, evalPolynomial_sum]
  simp_rw [evalPolynomial_mul, evalPolynomial_X]
  simp [evalPolynomial, Matrix.mulVec, dotProduct,
    symplecticGlMatrixOfPoint, symplecticGlEntryCoordinate, mul_comm]

private lemma symplecticLinearPointMulEquivOf_apply
    {m : ℕ}
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m))
    (c : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (x : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    symplecticLinearPointMulEquivOf e x (e.equivFun.symm c) =
      e.equivFun.symm ((symplecticGlMatrixOfPoint (k := k) x).mulVec c) := by
  change (glPointEquivOf k (symplecticStandardSpace (k := k) m) e x).1
      (e.equivFun.symm c) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [map_sum, map_smul, symplecticGlPointEquivOf_apply_basis]
  apply e.equivFun.injective
  rw [e.equivFun.apply_symm_apply]
  simp only [map_sum, map_smul, e.equivFun.apply_symm_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

private noncomputable def bilinearPreservationPolynomial
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m))
    (c d : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k) :
    MvPolynomial (glVarietyOf k (symplecticStandardSpace (k := k) m)).Coordinates k :=
  (∑ i, ∑ j,
      MvPolynomial.C (B (e i) (e j)) *
        symplecticTransformedCoordinatePolynomial (k := k) c i *
        symplecticTransformedCoordinatePolynomial (k := k) d j) -
    MvPolynomial.C (B (e.equivFun.symm c) (e.equivFun.symm d))

private lemma eval_bilinearPreservationPolynomial
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m))
    (c d : Fin (Module.finrank k (symplecticStandardSpace (k := k) m)) → k)
    (x : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    evalPolynomial x.val (bilinearPreservationPolynomial (k := k) B e c d) =
      B (symplecticLinearPointMulEquivOf e x (e.equivFun.symm c))
          (symplecticLinearPointMulEquivOf e x (e.equivFun.symm d)) -
        B (e.equivFun.symm c) (e.equivFun.symm d) := by
  let y := symplecticLinearPointMulEquivOf e x (e.equivFun.symm c)
  let z := symplecticLinearPointMulEquivOf e x (e.equivFun.symm d)
  have hy (i : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
      e.repr y i = (symplecticGlMatrixOfPoint (k := k) x).mulVec c i := by
    dsimp [y]
    rw [symplecticLinearPointMulEquivOf_apply]
    exact congrFun (e.equivFun.apply_symm_apply _) i
  have hz (i : Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) :
      e.repr z i = (symplecticGlMatrixOfPoint (k := k) x).mulVec d i := by
    dsimp [z]
    rw [symplecticLinearPointMulEquivOf_apply]
    exact congrFun (e.equivFun.apply_symm_apply _) i
  have eval_sub (p q : MvPolynomial
      (glVarietyOf k (symplecticStandardSpace (k := k) m)).Coordinates k) :
      evalPolynomial x.val (p - q) = evalPolynomial x.val p - evalPolynomial x.val q := by
    simp [evalPolynomial]
  rw [bilinearPreservationPolynomial, eval_sub, evalPolynomial_sum]
  simp_rw [evalPolynomial_sum, evalPolynomial_mul,
    eval_symplecticTransformedCoordinatePolynomial]
  simp only [evalPolynomial, MvPolynomial.eval₂_C, RingHom.id_apply]
  dsimp [y, z] at hy hz
  congr 1
  rw [← Matrix.toBilin_toMatrix e B, Matrix.toBilin_apply]
  simp_rw [LinearMap.BilinForm.toMatrix_apply]
  rw [Matrix.toBilin_toMatrix]
  simp_rw [← hy, ← hz]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

public noncomputable def bilinearIsometryGLSubgroup
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    Subgroup (Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :=
  (bilinearIsometrySubgroup B).comap (symplecticLinearPointMulEquivOf e).toMonoidHom

public lemma bilinearIsometryGLSubgroup_isZariskiClosed
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    IsZariskiClosed (glVarietyOf k (symplecticStandardSpace (k := k) m))
      (bilinearIsometryGLSubgroup (k := k) B e : Set
        (Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m)))) := by
  refine ⟨{p | ∃ c d, p = bilinearPreservationPolynomial (k := k) B e c d}, ?_⟩
  ext x
  constructor
  · intro hx p hp
    obtain ⟨c, d, rfl⟩ := hp
    rw [eval_bilinearPreservationPolynomial]
    change symplecticLinearPointMulEquivOf e x ∈ bilinearIsometrySubgroup B at hx
    rw [mem_bilinearIsometrySubgroup] at hx
    exact sub_eq_zero.mpr (hx _ _)
  · intro hx
    change symplecticLinearPointMulEquivOf e x ∈ bilinearIsometrySubgroup B
    rw [mem_bilinearIsometrySubgroup]
    intro v w
    let c := e.equivFun v
    let d := e.equivFun w
    have h := hx (bilinearPreservationPolynomial (k := k) B e c d) ⟨c, d, rfl⟩
    rw [eval_bilinearPreservationPolynomial] at h
    simpa [c, d] using sub_eq_zero.mp h

public noncomputable def bilinearIsometryClosedSubgroup
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    ClosedSubgroup (glVarietyOf k (symplecticStandardSpace (k := k) m)) :=
  ClosedSubgroup.ofSubgroup (bilinearIsometryGLSubgroup (k := k) B e)
    (bilinearIsometryGLSubgroup_isZariskiClosed (k := k) B e)

public theorem bilinearIsometryClosedSubgroup_carrier
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m))
    (g : Variety.Point (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    g ∈ (bilinearIsometryClosedSubgroup (k := k) B e).toSubgroup ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m) e g) ∈
        bilinearIsometrySubgroup B := by
  rfl

public noncomputable def bilinearIsometryClosedSubgroupPoints
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    let H := bilinearIsometryClosedSubgroup (k := k) B e
    letI := H.carrierAlgebraicGroup
    Variety.Point H.carrierVariety ≃* bilinearIsometrySubgroup B := by
  let H := bilinearIsometryClosedSubgroup (k := k) B e
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  let restrictEquiv : H.toSubgroup ≃* bilinearIsometrySubgroup B :=
    { toFun := fun x => ⟨symplecticLinearPointMulEquivOf e x.1, x.2⟩
      invFun := fun y => ⟨(symplecticLinearPointMulEquivOf e).symm y.1, by
        change symplecticLinearPointMulEquivOf e ((symplecticLinearPointMulEquivOf e).symm y.1) ∈
          bilinearIsometrySubgroup B
        rw [(symplecticLinearPointMulEquivOf e).apply_symm_apply]
        exact y.2⟩
      left_inv := fun x => Subtype.ext ((symplecticLinearPointMulEquivOf e).symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext ((symplecticLinearPointMulEquivOf e).apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext ((symplecticLinearPointMulEquivOf e).map_mul x.1 y.1) }
  exact pointEquiv.trans restrictEquiv

public theorem bilinearIsometryClosedSubgroup_linear_points
    {m : ℕ}
    (B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m))
    (e : Module.Basis (Fin (Module.finrank k (symplecticStandardSpace (k := k) m))) k
      (symplecticStandardSpace (k := k) m)) :
    let H := bilinearIsometryClosedSubgroup (k := k) B e
    letI := H.carrierAlgebraicGroup
    ∀ x, LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m) e
            (H.inclusion.onPoints x)) =
        (bilinearIsometryClosedSubgroupPoints (k := k) B e x).1 := by
  dsimp only
  intro x
  rfl

public noncomputable def symplecticMatrix (m : ℕ)
    (f : symplecticStandardSpace (k := k) m ≃ₗ[k] symplecticStandardSpace (k := k) m) :
    Matrix (symplecticStandardIndex m) (symplecticStandardIndex m) k :=
  LinearMap.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
    (Pi.basisFun k (symplecticStandardIndex m)) f

omit [IsAlgClosed k] in
public lemma mem_bilinearIsometrySubgroup_iff_symplecticMatrix
    (m : ℕ)
    (f : symplecticStandardSpace (k := k) m ≃ₗ[k] symplecticStandardSpace (k := k) m) :
    f ∈ bilinearIsometrySubgroup
        (Matrix.toBilin' (Matrix.J (Fin m) k)) ↔
      symplecticMatrix (k := k) m f ∈ Matrix.symplecticGroup (Fin m) k := by
  let B : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m) :=
    Matrix.toBilin' (Matrix.J (Fin m) k)
  let A := symplecticMatrix (k := k) m f
  have hmat : LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
      (B.comp f.toLinearMap f.toLinearMap) = Matrix.transpose A * Matrix.J (Fin m) k * A := by
    rw [LinearMap.BilinForm.toMatrix_comp
      (Pi.basisFun k (symplecticStandardIndex m)) (Pi.basisFun k (symplecticStandardIndex m)) B
      f.toLinearMap f.toLinearMap]
    rw [show LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m)) B =
      Matrix.J (Fin m) k by
        rw [show B = Matrix.toBilin' (Matrix.J (Fin m) k) by rfl]
        rw [LinearMap.BilinForm.toMatrix_basisFun,
          LinearMap.BilinForm.toMatrix'_toBilin']]
    rfl
  constructor
  · intro hf
    rw [SymplecticGroup.mem_iff']
    have heq : B.comp f.toLinearMap f.toLinearMap = B := by
      apply LinearMap.BilinForm.ext
      intro v w
      rw [LinearMap.BilinForm.comp_apply]
      exact (mem_bilinearIsometrySubgroup _ _).mp hf v w
    have hmatrixeq := congrArg
      (LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m))) heq
    calc
      Matrix.transpose A * Matrix.J (Fin m) k * A =
          LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
            (B.comp f.toLinearMap f.toLinearMap) := hmat.symm
      _ = LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m)) B := hmatrixeq
      _ = Matrix.J (Fin m) k := by
        rw [show B = Matrix.toBilin' (Matrix.J (Fin m) k) by rfl]
        rw [LinearMap.BilinForm.toMatrix_basisFun,
          LinearMap.BilinForm.toMatrix'_toBilin']
  · intro hA
    have hmat' : LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m))
        (B.comp f.toLinearMap f.toLinearMap) =
        LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m)) B := by
      rw [hmat]
      rw [SymplecticGroup.mem_iff'.mp hA]
      rw [show LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m)) B =
        Matrix.J (Fin m) k by
          rw [show B = Matrix.toBilin' (Matrix.J (Fin m) k) by rfl]
          rw [LinearMap.BilinForm.toMatrix_basisFun,
            LinearMap.BilinForm.toMatrix'_toBilin']]
    have heq : B.comp f.toLinearMap f.toLinearMap = B :=
      (LinearMap.BilinForm.toMatrix (Pi.basisFun k (symplecticStandardIndex m))).injective hmat'
    rw [mem_bilinearIsometrySubgroup]
    exact fun v w => (congrArg
      (fun C : LinearMap.BilinForm k (symplecticStandardSpace (k := k) m) => C v w) heq)

public noncomputable def standardSymplecticClosedSubgroup (m : ℕ) :
    ClosedSubgroup (glVarietyOf k (symplecticStandardSpace (k := k) m)) :=
  bilinearIsometryClosedSubgroup (k := k)
    (Matrix.toBilin' (Matrix.J (Fin m) k)) (symplecticStandardBasis (k := k) m)

public theorem standardSymplecticClosedSubgroup_carrier
    (m : ℕ) (g : Variety.Point
      (glVarietyOf k (symplecticStandardSpace (k := k) m))) :
    g ∈ (standardSymplecticClosedSubgroup (k := k) m).toSubgroup ↔
      LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m)
            (symplecticStandardBasis (k := k) m) g) ∈
        bilinearIsometrySubgroup (Matrix.toBilin' (Matrix.J (Fin m) k)) := by
  exact bilinearIsometryClosedSubgroup_carrier (k := k)
    (Matrix.toBilin' (Matrix.J (Fin m) k)) (symplecticStandardBasis (k := k) m) g

public noncomputable def standardSymplecticClosedSubgroupPoints (m : ℕ) :
    let H := standardSymplecticClosedSubgroup (k := k) m
    letI := H.carrierAlgebraicGroup
    Variety.Point H.carrierVariety ≃*
      bilinearIsometrySubgroup (Matrix.toBilin' (Matrix.J (Fin m) k)) := by
  exact bilinearIsometryClosedSubgroupPoints (k := k)
    (Matrix.toBilin' (Matrix.J (Fin m) k)) (symplecticStandardBasis (k := k) m)

public theorem standardSymplecticClosedSubgroup_linear_points (m : ℕ) :
    let H := standardSymplecticClosedSubgroup (k := k) m
    letI := H.carrierAlgebraicGroup
    ∀ x, LinearMap.GeneralLinearGroup.generalLinearEquiv k
          (symplecticStandardSpace (k := k) m)
          (glPointEquivOf k (symplecticStandardSpace (k := k) m)
            (symplecticStandardBasis (k := k) m) (H.inclusion.onPoints x)) =
        (standardSymplecticClosedSubgroupPoints (k := k) m x).1 := by
  exact bilinearIsometryClosedSubgroup_linear_points (k := k)
    (Matrix.toBilin' (Matrix.J (Fin m) k)) (symplecticStandardBasis (k := k) m)

end Theory.AlgebraicGroup
