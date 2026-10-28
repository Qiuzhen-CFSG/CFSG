module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Point

universe u

namespace Theory.AlgebraicGroup.Bor1

open CategoryTheory
open AlgebraicGeometry
open Theory.AlgebraicGroup
open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
open MonObj MonoidalCategory CartesianMonoidalCategory in
/-- The coordinate ring of an affine algebraic group over an algebraically
closed field is smooth over the base field. -/
public theorem polynomialFunction_smooth_of_algebraicGroup
    (G : Variety k) [AlgebraicGroup G] :
    Algebra.Smooth k (Variety.PolynomialFunction G) := by
  let C : Subalgebra k (Variety.PolynomialFunction G) := ⊤
  letI : Algebra.FiniteType k (Variety.PolynomialFunction G) :=
    polynomialFunction_finiteType G
  letI : IsReduced C := isReduced_of_injective C.val Subtype.val_injective
  let e : C ≃ₐ[k] Variety.PolynomialFunction G := Subalgebra.topEquiv
  letI : Algebra.FiniteType k C :=
    Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  have hcomul : ∀ q, q ∈ C → ∃ w : C ⊗[k] C,
      TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
        coordinateComultiplication G q := by
    intro q hq
    let E := Algebra.TensorProduct.congr e e
    let w := E.symm (coordinateComultiplication G q)
    refine ⟨w, ?_⟩
    change E w = _
    exact E.apply_symm_apply _
  have hantipode : ∀ q, q ∈ C → coordinateAntipode G q ∈ C := by
    simp [C]
  letI : HopfAlgebra k C :=
    coordinateSubalgebraHopfAlgebra G C hcomul hantipode
  letI : Algebra (CommRingCat.of k) (CommRingCat.of C) := inferInstance
  letI : Algebra.FiniteType (CommRingCat.of k) (CommRingCat.of C) :=
    inferInstance
  let f := (((Spec (CommRingCat.of C)).asOver
    (Spec (CommRingCat.of k))).hom)
  letI : LocallyOfFiniteType f :=
    locallyOfFiniteType_specOverSpec
  letI : IsReduced
      (((Spec (CommRingCat.of C)).asOver
        (Spec (CommRingCat.of k))).left) := by
    change IsReduced (Spec (CommRingCat.of C))
    infer_instance
  letI : GrpObj (Over.mk f) :=
    instGrpObjSpecAsOverSpec
      (R := CommRingCat.of k) (A := CommRingCat.of C)
  have hsmooth : Smooth f := by
    have := LocallyOfFiniteType.jacobsonSpace f
    have : Nonempty
        (((Spec (CommRingCat.of C)).asOver
          (Spec (CommRingCat.of k))).left) :=
      ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      ← TopologicalSpace.Opens.coe_eq_univ, ← not_ne_iff,
      ← Set.nonempty_compl]
    intro H
    obtain ⟨x, hx, hxc⟩ :=
      nonempty_inter_closedPoints H
        f.smoothLocus.2.isClosed_compl.isLocallyClosed
    obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ :=
      nonempty_inter_closedPoints
        f.dense_smoothLocus_of_perfectField.nonempty
        f.smoothLocus.2.isLocallyClosed
    let x' : 𝟙_ _ ⟶ Over.mk f :=
      Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
    let y' : 𝟙_ _ ⟶ Over.mk f :=
      Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
    let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
      GrpObj.mulRight (A := Over.mk f) y'
    have hα : x' ≫ α.hom = y' := by
      dsimp only [Iso.trans_hom, Iso.symm_hom, α]
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      simp [comp_lift_assoc]
    have hα' : α.hom.left x = y := by
      simpa [x', y', pointEquivClosedPoint] using
        congr(($hα).left (IsLocalRing.closedPoint k))
    rw! [← hα', ← α.hom.left.mem_preimage,
      Scheme.Hom.preimage_smoothLocus_eq,
      show α.hom.left ≫ f = f from α.hom.w] at hy
    exact hx hy
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap k C))) at hsmooth
  have hr : RingHom.Smooth (algebraMap k C) :=
    HasRingHomProperty.Spec_iff.mp hsmooth
  have hC : Algebra.Smooth k C := RingHom.smooth_algebraMap.mp hr
  exact Algebra.Smooth.of_equiv e

end Theory.AlgebraicGroup.Bor1
