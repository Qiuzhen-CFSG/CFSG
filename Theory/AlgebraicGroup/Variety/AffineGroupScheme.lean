module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Bialgebra
public import Theory.AlgebraicGroup.Irreducible.Product
public import Theory.AlgebraicGroup.Variety.Complete

set_option linter.style.haveILetI false

/-!
# Affine algebraic groups as group schemes

This module realizes a presented affine algebraic group as the corresponding
affine group scheme.  The coordinate Hopf algebra is constructed from the
existing algebraic-group multiplication, identity, and inverse morphisms; its
Hopf laws are proved on rational points by the polynomial-function
extensionality API.  Mathlib's affine `Spec` construction turns that Hopf
algebra into a group object over `Spec k`, and the group object on
`Geometric.ofAffine G` is obtained by transporting across the canonical
coordinate-ring equivalence.

The smoothness statements expose the standard group-scheme regularity theorem:
geometrically reduced, finite-type group schemes are smooth, and over an
algebraically closed field this also gives the reduced finite-type form used
for `Geometric.ofAffine G`.  When the original algebraic group is connected,
the existing irreducibility theorem for connected algebraic groups makes its
coordinate ring a domain, hence the affine spectrum is irreducible and
therefore connected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open MonObj MonoidalCategory CartesianMonoidalCategory

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k]

namespace Variety.Geometric

/-- The affine scheme attached to a presented affine algebraic group is a group
object over the base field. -/
@[instance_reducible]
public noncomputable instance ofAffine_grpObj
    (G : Variety k) [AlgebraicGroup G] :
    GrpObj (Over.mk (ofAffine G).structureMap) := by
  letI : HopfAlgebra k G.PolynomialFunction := coordinateHopfAlgebra G
  let source : Over (Spec (.of k)) :=
    (Spec (.of G.PolynomialFunction)).asOver (Spec (.of k))
  let target : Over (Spec (.of k)) :=
    Over.mk (ofAffine G).structureMap
  haveI : GrpObj source := by
    change GrpObj ((Spec (.of G.PolynomialFunction)).asOver (Spec (.of k)))
    infer_instance
  let eRing :
      CommRingCat.of (coordinateRing G) ≅ CommRingCat.of G.PolynomialFunction :=
    (coordinateRingAlgEquivPolynomialFunction G).toRingEquiv.toCommRingCatIso
  let eScheme : Spec (.of G.PolynomialFunction) ≅ Spec (.of (coordinateRing G)) :=
    Scheme.Spec.mapIso eRing.op
  have hover : eScheme.hom ≫ target.hom = source.hom := by
    dsimp [eScheme, eRing, target, source, ofAffine]
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (coordinateRingAlgEquivPolynomialFunction G).commutes r
  exact @GrpObj.ofIso _ _ _ source target inferInstance (Over.isoMk eScheme hover)

/-- The coordinate ring of a connected affine algebraic group is a domain. -/
public theorem ofAffine_coordinateRing_isDomain_of_isConnected
    (G : Variety k) [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    IsDomain (coordinateRing G) :=
  connectedAlgebraicGroup_coordinateRing_domain G hG

/-- A connected affine algebraic group has irreducible affine spectrum. -/
public theorem ofAffine_isIrreducible_of_isConnected
    (G : Variety k) [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    IsIrreducible (ofAffine G) := by
  change IrreducibleSpace (Spec (.of (coordinateRing G)))
  letI : IsDomain (coordinateRing G) :=
    ofAffine_coordinateRing_isDomain_of_isConnected G hG
  infer_instance

/-- A connected affine algebraic group has connected affine spectrum. -/
public theorem ofAffine_isConnected_of_isConnected
    (G : Variety k) [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    IsConnected (ofAffine G) := by
  letI : IrreducibleSpace (ofAffine G).toScheme :=
    ofAffine_isIrreducible_of_isConnected G hG
  change ConnectedSpace (ofAffine G).toScheme
  infer_instance

/-- A geometrically reduced affine algebraic group scheme is smooth. -/
public theorem ofAffine_smooth_of_geometricallyReduced
    (G : Variety k) [AlgebraicGroup G]
    [GeometricallyReduced (ofAffine G).structureMap] :
    Smooth (ofAffine G).structureMap := by
  letI : GrpObj (Over.mk (ofAffine G).structureMap) :=
    ofAffine_grpObj G
  exact AlgebraicGeometry.smooth_of_grpObj (ofAffine G).structureMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem smooth_of_grpObj_of_isAlgClosed
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [GrpObj (Over.mk f)] [IsReduced X]
    [IsAlgClosed k] :
    Smooth f := by
  have := LocallyOfFiniteType.jacobsonSpace f
  have : Nonempty X :=
    ⟨η[Over.mk f].1 (IsLocalRing.closedPoint _)⟩
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  let x' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨x, hxc⟩).2
  let y' : 𝟙_ _ ⟶ Over.mk f := Over.homMk _ ((pointEquivClosedPoint f).symm ⟨y, hyc⟩).2
  let α := (GrpObj.mulRight (A := Over.mk f) x').symm ≪≫
    (GrpObj.mulRight (A := Over.mk f) y')
  have hα : x' ≫ α.hom = y' := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left x = y := by
    simpa [x', y', pointEquivClosedPoint] using
      congr(($hα).left (IsLocalRing.closedPoint k))
  rw! [← hα', ← α.hom.left.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq,
    show α.hom.left ≫ f = f from α.hom.w] at hy
  exact hx hy

/-- Over an algebraically closed field, the reduced finite-type affine group
scheme attached to a presented affine algebraic group is smooth. -/
public theorem ofAffine_smooth
    (G : Variety k) [AlgebraicGroup G] [IsAlgClosed k] :
    Smooth (ofAffine G).structureMap := by
  letI : GrpObj (Over.mk (ofAffine G).structureMap) :=
    ofAffine_grpObj G
  exact smooth_of_grpObj_of_isAlgClosed (ofAffine G).structureMap

end Variety.Geometric

end Theory.AlgebraicGroup
