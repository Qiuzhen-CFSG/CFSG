module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.TorusRigidity
public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponentGeometry
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.StabilizerFiber

/-!
# Rigidity on the actual fixed-component preimage

The inverse image of a torus-fixed component under the Borel orbit morphism
consists of points y for which y⁻¹Sy lies in the original Borel. We construct
the regular conjugation family with values in that Borel by the reduced
closed-immersion lifting property. Composing with any actual torus-valued
Borel homomorphism and applying connected-family rigidity gives q(y⁻¹sy)=q(s).

This is Borel, *Linear Algebraic Groups*, §11.15; the original component,
orbit map, subgroup inclusions, and quotient map are retained.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
open BorelGeometricConjugacy Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup

private theorem closed_range_of_points {V W : Variety.Geometric k}
    (C : ClosedSubvariety V) (f : Variety.Geometric.Morphism W V)
    (h : ∀ p : Point W, ∃ q : Point C.toGeometric, C.inclusion q = f p) :
    Set.range f.hom ⊆ Set.range C.inclusion.hom := by
  let : JacobsonSpace W.toScheme := LocallyOfFiniteType.jacobsonSpace W.structureMap
  have hclosed : IsClosed (f.hom ⁻¹' Set.range C.inclusion.hom) :=
    C.inclusion.hom.isClosedEmbedding.isClosed_range.preimage f.hom.continuous
  have hsub : closedPoints W.toScheme ⊆ f.hom ⁻¹' Set.range C.inclusion.hom := by
    intro z hz
    let p := (pointEquivClosedPoint W.structureMap).symm ⟨z, hz⟩
    obtain ⟨q, hq⟩ := h p
    have hp : p.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint W.structureMap).apply_symm_apply ⟨z, hz⟩)
    refine ⟨q.1 (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg (fun r : Point V => r.1 (IsLocalRing.closedPoint k)) hq
    change C.inclusion.hom (q.1 (IsLocalRing.closedPoint k)) =
      f.hom (p.1 (IsLocalRing.closedPoint k)) at he
    simpa only [hp] using he
  have hall := closure_minimal hsub hclosed
  rw [closure_closedPoints] at hall
  rintro _ ⟨w, rfl⟩
  exact hall (Set.mem_univ w)

private noncomputable def liftClosed {V W : Variety.Geometric k}
    (C : ClosedSubvariety V) (f : Variety.Geometric.Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) :
    Variety.Geometric.Morphism W C.toGeometric := by
  have : QuasiCompact (f.hom ≫ V.structureMap) := f.commutes.symm ▸ inferInstance
  let : QuasiCompact f.hom := QuasiCompact.of_comp f.hom V.structureMap
  let Z : Closeds V.toScheme :=
    ⟨Set.range C.inclusion.hom, C.inclusion.hom.isClosedEmbedding.isClosed_range⟩
  have hv : Scheme.IdealSheafData.vanishingIdeal Z ≤ f.hom.ker :=
    vanishingIdeal_le_ker_of_isReduced Z f.hom hf
  have hc : C.inclusion.hom.ker ≤ Scheme.IdealSheafData.vanishingIdeal Z :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
      C.inclusion.hom.range_subset_ker_support
  exact { hom := IsClosedImmersion.lift C.inclusion.hom f.hom (hc.trans hv)
          commutes := by
            rw [← C.inclusion.commutes, ← Category.assoc,
              IsClosedImmersion.lift_fac, f.commutes] }

omit [IsAlgClosed k] in
private theorem liftClosed_apply {V W : Variety.Geometric k}
    (C : ClosedSubvariety V) (f : Variety.Geometric.Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) (x : Point W) :
    C.inclusion (liftClosed C f hf x) = f x := by
  apply Subtype.ext
  change (x.1 ≫ IsClosedImmersion.lift _ _ _) ≫ C.inclusion.hom = x.1 ≫ f.hom
  rw [Category.assoc, IsClosedImmersion.lift_fac]

private noncomputable def subgroupClosedSubvariety (B : ClosedSubgroup H) :
    ClosedSubvariety (ofAffine H) where
  toGeometric := ofAffine B.carrierVariety
  inclusion := ofAffine_morphism B.inclusion.toVariety
  isClosedImmersion := ofAffine_closedSubgroup_inclusion_isClosedImmersion B

public theorem point_mem_componentPreimage_iff {B : ClosedSubgroup H}
    (M : CompleteModel B) (X : ClosedSubvariety M.variety) (y : Point (ofAffine H)) :
    y ∈ Set.range (componentPreimage M X).inclusion ↔
      M.action.toMulAction.smul (affinePointEquiv H y) (modelBasePoint M) ∈ Set.range X.inclusion := by
  rw [(componentPreimage M X).inclusion.point_mem_range_iff_closedPoint_mem_range,
    componentPreimage_range]
  change (M.action.orbitMorphismAt (modelBasePoint M)).hom
    (y.1 (IsLocalRing.closedPoint k)) ∈ Set.range X.inclusion.hom ↔ _
  rw [← Variety.Geometric.Morphism.apply_closedPoint,
    ← X.inclusion.point_mem_range_iff_closedPoint_mem_range]
  have h := M.action.orbitMorphismAt_apply (modelBasePoint M) (affinePointEquiv H y)
  rw [Equiv.symm_apply_apply] at h
  rw [h]

public theorem componentPreimage_conjugate_mem {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s : Variety.Point S.carrierVariety) :
    (affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y))⁻¹ *
      S.inclusion.onPoints s *
      affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y) ∈ B.toSubgroup := by
  let g := affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y)
  obtain ⟨x, hx⟩ := (point_mem_componentPreimage_iff M (fixedComponent M S Z)
    ((componentPreimage M (fixedComponent M S Z)).inclusion y)).mp ⟨y, rfl⟩
  apply (modelBasePoint_stabilizer M _).mp
  let := M.action.toMulAction
  change (g⁻¹ * S.inclusion.onPoints s * g) • modelBasePoint M = modelBasePoint M
  let v : Point M.variety := (fixedComponent M S Z).inclusion x
  have hv : v = g • modelBasePoint M := hx
  have hfix : S.inclusion.onPoints s • v = v := fixedComponent_fixed M S Z x (S.pointEquiv s)
  calc
    _ = g⁻¹ • (S.inclusion.onPoints s • (g • modelBasePoint M)) := by rw [mul_smul, mul_smul]
    _ = g⁻¹ • (S.inclusion.onPoints s • v) :=
      congrArg (fun z : Point M.variety => g⁻¹ • (S.inclusion.onPoints s • z)) hv.symm
    _ = g⁻¹ • v := congrArg (fun z : Point M.variety => g⁻¹ • z) hfix
    _ = g⁻¹ • (g • modelBasePoint M) := congrArg (fun z : Point M.variety => g⁻¹ • z) hv
    _ = modelBasePoint M := by rw [← mul_smul, inv_mul_cancel, one_smul]

private noncomputable def inverseConjugationPair (H : Variety k) [AlgebraicGroup H] :
    Variety.Morphism (Variety.prod H H) H :=
  (mulMorphism H).comp
    (((mulMorphism H).comp
      (((invMorphism H).comp (Variety.Morphism.fst H H)).pair (Variety.Morphism.snd H H))).pair
        (Variety.Morphism.fst H H))

public noncomputable def componentConjugationAmbient {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    Variety.Geometric.Morphism
      (Variety.Geometric.prod (componentPreimage M (fixedComponent M S Z)).toGeometric (ofAffine S.carrierVariety))
      (ofAffine H) :=
  (Variety.Geometric.Morphism.pair
    ((fst _ _).comp (componentPreimage M (fixedComponent M S Z)).inclusion)
    ((snd _ _).comp (ofAffine_morphism S.inclusion.toVariety))).comp
      (ofAffineProductMorphism (inverseConjugationPair H))

public theorem componentConjugationAmbient_apply {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s : Variety.Point S.carrierVariety) :
    affinePointEquiv H (componentConjugationAmbient M S Z
      (prodPoint y ((affinePointEquiv S.carrierVariety).symm s))) =
    (affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y))⁻¹ *
      S.inclusion.onPoints s *
      affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y) := by
  unfold componentConjugationAmbient
  rw [Variety.Geometric.Morphism.comp_apply_point, Variety.Geometric.Morphism.pair_apply,
    Variety.Geometric.Morphism.comp_apply_point, Variety.Geometric.Morphism.comp_apply_point,
    fst_prodPoint, snd_prodPoint, affinePointEquiv_ofAffineProductMorphism_prodPoint,
    affinePointEquiv_ofAffine_morphism, Equiv.apply_symm_apply]
  rfl

private theorem componentConjugationAmbient_range {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    Set.range (componentConjugationAmbient M S Z).hom ⊆
      Set.range (ofAffine_morphism B.inclusion.toVariety).hom := by
  apply closed_range_of_points (subgroupClosedSubvariety B)
  intro p
  obtain ⟨⟨y, s⟩, rfl⟩ := (prodPointEquiv _ _).symm.surjective p
  apply (ofAffine_closedSubgroup_inclusion_point_range B _).mpr
  change affinePointEquiv H (componentConjugationAmbient M S Z (prodPoint y s)) ∈ B.toSubgroup
  rw [← (affinePointEquiv S.carrierVariety).symm_apply_apply s]
  erw [componentConjugationAmbient_apply]
  exact componentPreimage_conjugate_mem M S Z y _

public noncomputable def componentConjugationFamily {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    Variety.Geometric.Morphism
      (Variety.Geometric.prod (componentPreimage M (fixedComponent M S Z)).toGeometric (ofAffine S.carrierVariety))
      (ofAffine B.carrierVariety) :=
  liftClosed (subgroupClosedSubvariety B) (componentConjugationAmbient M S Z)
    (componentConjugationAmbient_range M S Z)

public theorem componentConjugationFamily_apply {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s : Variety.Point S.carrierVariety) :
    B.inclusion.onPoints (torusFamilyPoint (componentConjugationFamily M S Z) y s) =
    (affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y))⁻¹ *
      S.inclusion.onPoints s *
      affinePointEquiv H ((componentPreimage M (fixedComponent M S Z)).inclusion y) := by
  have h := liftClosed_apply (subgroupClosedSubvariety B) (componentConjugationAmbient M S Z)
    (componentConjugationAmbient_range M S Z) (prodPoint y ((affinePointEquiv S.carrierVariety).symm s))
  exact (affinePointEquiv_ofAffine_morphism B.inclusion.toVariety _).symm.trans
    ((congrArg (affinePointEquiv H) h).trans (componentConjugationAmbient_apply M S Z y s))

public theorem componentConjugationFamily_one {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric) :
    torusFamilyPoint (componentConjugationFamily M S Z) y 1 = 1 := by
  apply B.inclusion_injective
  rw [componentConjugationFamily_apply, map_one, map_one]
  group

public theorem componentConjugationFamily_mul {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s t : Variety.Point S.carrierVariety) :
    torusFamilyPoint (componentConjugationFamily M S Z) y (s * t) =
      torusFamilyPoint (componentConjugationFamily M S Z) y s *
        torusFamilyPoint (componentConjugationFamily M S Z) y t := by
  apply B.inclusion_injective
  rw [map_mul, componentConjugationFamily_apply, componentConjugationFamily_apply,
    componentConjugationFamily_apply, map_mul]
  group

private theorem quotientFamily_apply {B : ClosedSubgroup H}
    (M : CompleteModel B) (S : ClosedSubgroup H)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    {Q : Variety k} [AlgebraicGroup Q] (q : AlgebraicGroup.Morphism B.carrierVariety Q)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s : Variety.Point S.carrierVariety) :
    torusFamilyPoint ((componentConjugationFamily M S Z).comp (ofAffine_morphism q.toVariety)) y s =
      q.onPoints (torusFamilyPoint (componentConjugationFamily M S Z) y s) := by
  rw [torusFamilyPoint, Variety.Geometric.Morphism.comp_apply_point,
    affinePointEquiv_ofAffine_morphism]
  rfl

public theorem componentPreimage_quotient_conjugation_constant {B : ClosedSubgroup H}
    (M : CompleteModel B) (hH : Variety.IsConnected H) (hB : IsBorelSubgroup B)
    (S : ClosedSubgroup H) (hS : IsSubtorus S) (hSB : S ≤ B)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (x : Point (fixedComponent M S Z).toGeometric)
    (hx : (fixedComponent M S Z).inclusion x = modelBasePoint M)
    {Q : Variety k} [AlgebraicGroup Q] (q : AlgebraicGroup.Morphism B.carrierVariety Q)
    (hQ : IsTorus Q)
    (y : Point (componentPreimage M (fixedComponent M S Z)).toGeometric)
    (s : Variety.Point S.carrierVariety) :
    q.onPoints (torusFamilyPoint (componentConjugationFamily M S Z) y s) =
      q.onPoints ((S.inclusion.codRestrictClosedSubgroup B
        (fun t => hSB (S.pointEquiv t).property)).onPoints s) := by
  let α := (componentConjugationFamily M S Z).comp (ofAffine_morphism q.toVariety)
  have hone : ∀ y, torusFamilyPoint α y 1 = 1 := by
    intro y
    rw [quotientFamily_apply, componentConjugationFamily_one, map_one]
  have hmul : ∀ y a b, torusFamilyPoint α y (a * b) =
      torusFamilyPoint α y a * torusFamilyPoint α y b := by
    intro y a b
    rw [quotientFamily_apply, quotientFamily_apply, quotientFamily_apply,
      componentConjugationFamily_mul, map_mul]
  obtain ⟨y0, hy0⟩ := (point_mem_componentPreimage_iff M (fixedComponent M S Z)
    ((affinePointEquiv H).symm 1)).mpr (by
      refine ⟨x, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hx.trans (M.action.toMulAction.one_smul (modelBasePoint M)).symm)
  have hc := torus_family_rigidity (fixedComponentPreimage_isConnected M hH hB S Z)
    hS hQ α hone hmul y y0 s
  rw [quotientFamily_apply, quotientFamily_apply] at hc
  rw [hc]
  congr 1
  apply B.inclusion_injective
  rw [componentConjugationFamily_apply, hy0, Equiv.apply_symm_apply,
    AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply]
  group
end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
