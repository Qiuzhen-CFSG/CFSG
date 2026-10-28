module

public import Theory.AlgebraicGroup.Instance.PSL
public import Theory.PGL2.Defs

/-!
# The affine PGL₂ carrier

Over an algebraically closed field, the tensor image of the two-dimensional
standard `SL₂` module is an affine closed subgroup of `SL₄`.  Its carrier
points are identified with the usual `PGL₂` points by first-isomorphism for
the tensor morphism, the explicit tensor-kernel calculation, and
`Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed`.  The quotient step
is therefore an explicit group quotient comparison, not an inference from
point-kernel equality alone.  The exported projection formula sends every
affine `SL₂` point to its canonical Mathlib `PGL₂` class.  The carrier inherits
polynomial multiplication and inversion from its ambient `SL₄` model.

The tensor-image construction is the standard projective-special-linear
construction from GLS3, Example 1.1.7, implemented in
`Theory.AlgebraicGroup.Instance.PSL`; the bridge to `PGL₂` is the canonical
Mathlib determinant-root equivalence for algebraically closed fields.
-/

open scoped MatrixGroups

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The canonical affine closed carrier for `PGL₂`, namely the tensor-image
carrier of the two-dimensional standard `SL₂` module. -/
public noncomputable abbrev pgl2ClosedSubgroup :
    ClosedSubgroup
      (slVariety k (Module.finrank k (Fin 2 → k) * Module.finrank k (Fin 2 → k))) :=
  pslClosedSubgroupOf k (Fin 2 → k)

/-- The affine variety underlying the canonical `PGL₂` carrier. -/
public noncomputable abbrev pgl2Variety : Variety k :=
  (pgl2ClosedSubgroup (k := k)).carrierVariety

/-- The inherited algebraic-group structure on the affine `PGL₂` carrier. -/
public noncomputable instance pgl2AlgebraicGroup :
    AlgebraicGroup (pgl2Variety (k := k)) :=
  (pgl2ClosedSubgroup (k := k)).carrierAlgebraicGroup

/-- Polynomial multiplication on the affine `PGL₂` carrier. -/
public lemma pgl2_mul_regular
    (i : (pgl2Variety (k := k)).Coordinates)
    (x y : Variety.Point (pgl2Variety (k := k))) :
    (x * y).val i =
      evalPolynomial (Sum.elim x.val y.val)
        ((pgl2AlgebraicGroup (k := k)).mulPolynomial i) :=
  (pgl2AlgebraicGroup (k := k)).mul_regular i x y

/-- Polynomial inversion on the affine `PGL₂` carrier. -/
public lemma pgl2_inv_regular
    (i : (pgl2Variety (k := k)).Coordinates)
    (x : Variety.Point (pgl2Variety (k := k))) :
    x⁻¹.val i = evalPolynomial x.val
      ((pgl2AlgebraicGroup (k := k)).invPolynomial i) :=
  (pgl2AlgebraicGroup (k := k)).inv_regular i x

/-- The tensor morphism whose closed image is the affine `PGL₂` carrier. -/
public noncomputable abbrev pgl2TensorMorphism :
    AlgebraicGroup.Morphism
      (slVariety k (Module.finrank k (Fin 2 → k)))
      (slVariety k (Module.finrank k (Fin 2 → k) * Module.finrank k (Fin 2 → k))) :=
  slTensorActionMorphism (k := k) (Module.finrank k (Fin 2 → k))

/-- The tensor morphism with codomain restricted to its canonical closed image. -/
@[expose] public noncomputable def pgl2Projection :
    AlgebraicGroup.Morphism
      (slVariety k (Module.finrank k (Fin 2 → k)))
      (pgl2Variety (k := k)) := by
  let P := pgl2ClosedSubgroup (k := k)
  exact pgl2TensorMorphism.codRestrictClosedSubgroup P (fun x => by
    exact ⟨x, rfl⟩)

/-- Including the restricted tensor morphism recovers the ambient tensor map. -/
public lemma pgl2Projection_inclusion_apply
    (x : Variety.Point (slVariety k (Module.finrank k (Fin 2 → k)))) :
    (pgl2ClosedSubgroup (k := k)).inclusion.onPoints
        (pgl2Projection (k := k) |>.onPoints x) =
      pgl2TensorMorphism.onPoints x := by
  exact Morphism.codRestrictClosedSubgroup_inclusion_apply
    pgl2TensorMorphism (pgl2ClosedSubgroup (k := k)) (fun x => by
      exact ⟨x, rfl⟩) x

/-- The tensor morphism has the center of `SL₂` as its point kernel. -/
public lemma pgl2TensorMorphism_kernel :
    (pgl2TensorMorphism (k := k)).kernel =
      Subgroup.center (Variety.Point
        (slVariety k (Module.finrank k (Fin 2 → k)))) := by
  exact slTensorActionMorphism_ker (k := k) (Module.finrank k (Fin 2 → k))

/-- The closed-image restriction has the same kernel as the tensor morphism. -/
public lemma pgl2Projection_kernel :
    (pgl2Projection (k := k)).kernel =
      Subgroup.center (Variety.Point
        (slVariety k (Module.finrank k (Fin 2 → k)))) := by
  calc
    (pgl2Projection (k := k)).kernel =
        (pgl2TensorMorphism (k := k)).kernel := by
      simpa [pgl2Projection] using
        (Morphism.codRestrictClosedSubgroup_kernel_eq
          pgl2TensorMorphism (pgl2ClosedSubgroup (k := k)) (fun x => by
            exact ⟨x, rfl⟩))
    _ = _ := pgl2TensorMorphism_kernel (k := k)

private lemma pgl2_center_map :
    Subgroup.map (slPointMulEquiv (k := k) (Module.finrank k (Fin 2 → k)))
      (Subgroup.center (Variety.Point
        (slVariety k (Module.finrank k (Fin 2 → k))))) =
      Subgroup.center (Matrix.SpecialLinearGroup
        (Fin (Module.finrank k (Fin 2 → k))) k) := by
  let e := slPointMulEquiv (k := k) (Module.finrank k (Fin 2 → k))
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx' : e x ∈ Subgroup.center _ :=
      (MulEquivClass.apply_mem_center_iff e).mpr hx
    exact hx'
  · rintro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    exact (MulEquivClass.apply_mem_center_iff e).mp hy

/-- The quotient of the affine `SL₂` points by the tensor kernel is its
projective-special-linear point group. -/
public noncomputable def pgl2SourceQuotientEquiv :
    Variety.Point (slVariety k (Module.finrank k (Fin 2 → k))) ⧸
        (pgl2TensorMorphism (k := k)).kernel ≃*
      Matrix.ProjectiveSpecialLinearGroup
        (Fin (Module.finrank k (Fin 2 → k))) k := by
  let e := slPointMulEquiv (k := k) (Module.finrank k (Fin 2 → k))
  let hker := pgl2TensorMorphism_kernel (k := k)
  let hcenter := pgl2_center_map (k := k)
  let eq : Variety.Point (slVariety k (Module.finrank k (Fin 2 → k))) ⧸
      (pgl2TensorMorphism (k := k)).kernel ≃*
      Variety.Point (slVariety k (Module.finrank k (Fin 2 → k))) ⧸
        Subgroup.center (Variety.Point
          (slVariety k (Module.finrank k (Fin 2 → k)))) :=
    QuotientGroup.quotientMulEquivOfEq hker
  exact eq.trans (QuotientGroup.congr
    (Subgroup.center (Variety.Point
      (slVariety k (Module.finrank k (Fin 2 → k)))))
    (Subgroup.center (Matrix.SpecialLinearGroup
      (Fin (Module.finrank k (Fin 2 → k))) k)) e hcenter)

/-- The source quotient equivalence sends the class of an affine `SL₂` point
to the class of its standard special-linear matrix. -/
@[simp] public lemma pgl2SourceQuotientEquiv_mk
    (x : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 → k)))) :
    pgl2SourceQuotientEquiv (k := k) (QuotientGroup.mk x) =
      QuotientGroup.mk
        (slPointEquiv (k := k) (Module.finrank k (Fin 2 → k)) x) := by
  simp [pgl2SourceQuotientEquiv]

/-- The usual `PGL₂` class represented by an affine `SL₂` point.  The small
dimension transport only identifies the computed finrank of `Fin 2 → k`
with `2`; the class itself is the canonical `SL₂ → PGL₂` map. -/
@[expose]
public noncomputable def pgl2SLPointClass (x : Variety.Point
    (slVariety k (Module.finrank k (Fin 2 → k)))) : PGL2 k :=
  let c : Matrix.ProjGenLinGroup
      (Fin (Module.finrank k (Fin 2 → k))) k ≃* PGL2 k := by
    rw [Module.finrank_fin_fun k]
  c (Matrix.SpecialLinearGroup.toPGL
    (slPointEquiv (Module.finrank k (Fin 2 → k)) x))

/-- Group-point equivalence between the affine carrier and `PGL₂`. -/
@[expose] public noncomputable def pgl2PointMulEquiv :
    Variety.Point (pgl2Variety (k := k)) ≃* PGL2 k := by
  let P := pgl2ClosedSubgroup (k := k)
  let eP := P.pointEquiv
  let ePmul : Variety.Point P.carrierVariety ≃* P.toSubgroup :=
    { toEquiv := eP
      map_mul' := by intro x y; rfl }
  let equot := pgl2SourceQuotientEquiv (k := k)
  let epsl := Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed
    (n := Fin (Module.finrank k (Fin 2 → k))) (F := k)
  have hP : P.toSubgroup = (pgl2TensorMorphism (k := k)).image := by
    rfl
  let ecarrier : Variety.Point P.carrierVariety ≃*
      (pgl2TensorMorphism (k := k)).image :=
    ePmul.trans (MulEquiv.subgroupCongr hP)
  have h : Variety.Point P.carrierVariety ≃*
      Matrix.ProjGenLinGroup (Fin (Module.finrank k (Fin 2 → k))) k :=
    ecarrier.trans
      (QuotientGroup.quotientKerEquivRange
        (pgl2TensorMorphism (k := k)).onPoints).symm |>.trans equot |>.trans epsl.symm
  let c : Matrix.ProjGenLinGroup
      (Fin (Module.finrank k (Fin 2 → k))) k ≃*
      Matrix.ProjGenLinGroup (Fin 2) k := by
    rw [Module.finrank_fin_fun k]
  exact h.trans c

/-- The point equivalence sends the tensor-image projection of an `SL₂`
point to the projective class of its standard two-dimensional matrix. -/
@[simp] public lemma pgl2PointMulEquiv_projection
    (x : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 → k)))) :
    pgl2PointMulEquiv (k := k) ((pgl2Projection (k := k)).onPoints x) =
      pgl2SLPointClass x := by
  let P := pgl2ClosedSubgroup (k := k)
  let eP := P.pointEquiv
  let ePmul : Variety.Point P.carrierVariety ≃* P.toSubgroup :=
    { toEquiv := eP
      map_mul' := by intro a b; rfl }
  let equot := pgl2SourceQuotientEquiv (k := k)
  let epsl := Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed
    (n := Fin (Module.finrank k (Fin 2 → k))) (F := k)
  have hP : P.toSubgroup = (pgl2TensorMorphism (k := k)).image := by
    rfl
  let ecarrier : Variety.Point P.carrierVariety ≃*
      (pgl2TensorMorphism (k := k)).image :=
    ePmul.trans (MulEquiv.subgroupCongr hP)
  let q := QuotientGroup.quotientKerEquivRange
    (pgl2TensorMorphism (k := k)).onPoints
  let c : Matrix.ProjGenLinGroup
      (Fin (Module.finrank k (Fin 2 → k))) k ≃* PGL2 k := by
    rw [Module.finrank_fin_fun k]
  change c (epsl.symm (equot (q.symm
    (ecarrier ((pgl2Projection (k := k)).onPoints x))))) = _
  have hquot : q.symm
      (ecarrier ((pgl2Projection (k := k)).onPoints x)) =
      (QuotientGroup.mk x :
        Variety.Point (slVariety k (Module.finrank k (Fin 2 → k))) ⧸
          (pgl2TensorMorphism (k := k)).kernel) := by
    apply q.injective
    calc
      q (q.symm _) = _ := q.apply_symm_apply _
      _ = q (QuotientGroup.mk x) := by
        apply Subtype.ext
        exact pgl2Projection_inclusion_apply (k := k) x
  rw [hquot, pgl2SourceQuotientEquiv_mk]
  unfold pgl2SLPointClass
  change c (epsl.symm _) = c
    (Matrix.SpecialLinearGroup.toPGL
      (slPointEquiv (Module.finrank k (Fin 2 → k)) x))
  congr 1
  apply epsl.injective
  rw [epsl.apply_symm_apply]
  have hnon : Nonempty (Fin (Module.finrank k (Fin 2 → k))) := by
    rw [Module.finrank_fin_fun k]
    infer_instance
  let _ : Nonempty (Fin (Module.finrank k (Fin 2 → k))) := hnon
  simp [epsl, Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosed,
    Matrix.ProjectiveSpecialLinearGroup.isoPSLOfAlgClosedOfNonempty,
    dif_pos hnon]
  rw [← Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  symm
  exact MulEquiv.ofBijective_apply_symm_apply _ _

@[simp] public lemma pgl2PointMulEquiv_one :
    pgl2PointMulEquiv (k := k) (1 : Variety.Point (pgl2Variety (k := k))) = 1 :=
  map_one _

@[simp] public lemma pgl2PointMulEquiv_mul
    (x y : Variety.Point (pgl2Variety (k := k))) :
    pgl2PointMulEquiv (k := k) (x * y) =
      pgl2PointMulEquiv (k := k) x * pgl2PointMulEquiv (k := k) y :=
  (pgl2PointMulEquiv (k := k)).map_mul x y

@[simp] public lemma pgl2PointMulEquiv_inv
    (x : Variety.Point (pgl2Variety (k := k))) :
    pgl2PointMulEquiv (k := k) x⁻¹ =
      (pgl2PointMulEquiv (k := k) x)⁻¹ :=
  (pgl2PointMulEquiv (k := k)).map_inv x

end Theory.AlgebraicGroup
