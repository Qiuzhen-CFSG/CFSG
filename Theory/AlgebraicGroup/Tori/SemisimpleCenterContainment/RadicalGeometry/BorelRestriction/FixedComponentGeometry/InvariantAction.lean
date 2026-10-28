module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponents
public import Theory.AlgebraicGroup.Variety.MorphicActionPullback

/-!
# The centralizer action on an actual fixed component

The centralizer preserves the reduced subgroup-fixed locus because its elements
commute with the acting subgroup. The action morphism factors through that
closed locus by reducedness and density of closed points.

A connected algebraic group preserves each irreducible component. To see this,
use the open locus belonging to just one component. The orbit of a rational point
there is irreducible, hence lies in that component. Density then extends the
invariance to the entire component, and the same reduced-factorization argument
constructs its regular action.

The exported action is on the published `fixedComponent` itself, with its
inclusion equivariant through the literal centralizer inclusion. Centralizer
connectedness is explicit; transitivity is neither assumed nor asserted here.
This is the component-invariance step of Borel, *Linear Algebraic Groups*,
§11.15 (`refs/KGroup/Bor1/Chapter4.tex`).
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open Theory.AlgebraicGroup
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {V : Geometric k}

private theorem closed_range_of_points {W : Geometric k}
    (C : ClosedSubvariety V) (f : Morphism W V)
    (h : ∀ p : Point W, ∃ q : Point C.toGeometric, C.inclusion q = f p) :
    Set.range f.hom ⊆ Set.range C.inclusion.hom := by
  letI : JacobsonSpace W.toScheme := LocallyOfFiniteType.jacobsonSpace W.structureMap
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

private noncomputable def liftClosed {W : Geometric k}
    (C : ClosedSubvariety V) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) : Morphism W C.toGeometric := by
  haveI : QuasiCompact (f.hom ≫ V.structureMap) := f.commutes.symm ▸ inferInstance
  letI : QuasiCompact f.hom := QuasiCompact.of_comp f.hom V.structureMap
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
private theorem liftClosed_fac {W : Geometric k}
    (C : ClosedSubvariety V) (f : Morphism W V)
    (hf : Set.range f.hom ⊆ Set.range C.inclusion.hom) :
    (liftClosed C f hf).comp C.inclusion = f := by
  apply Morphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

omit [IsAlgClosed k] in
private theorem inclusion_injective (C : ClosedSubvariety V) :
    Function.Injective (fun x : Point C.toGeometric => C.inclusion x) := by
  intro x y h
  apply Subtype.ext
  apply (cancel_mono C.inclusion.hom).mp
  exact congrArg Subtype.val h

namespace MorphicAction
private noncomputable def componentAmbientAction (A : MorphicAction G V)
    (C : ClosedSubvariety V) : Morphism (prod (ofAffine G) C.toGeometric) V :=
  (Morphism.pair (fst _ _) ((snd _ _).comp C.inclusion)).comp A.actionMorphism

private theorem componentAmbientAction_apply (A : MorphicAction G V)
    (C : ClosedSubvariety V) (g : Variety.Point G) (x : Point C.toGeometric) :
    A.componentAmbientAction C (prodPoint ((affinePointEquiv G).symm g) x) =
      A.toMulAction.smul g (C.inclusion x) := by
  change A.actionMorphism (Morphism.pair _ _ _) = _
  rw [Morphism.pair_apply, fst_prodPoint, Morphism.comp_apply_point, snd_prodPoint]
  exact A.actionMorphism_apply g _

private theorem componentAmbientAction_range (A : MorphicAction G V)
    (C : ClosedSubvariety V)
    (hC : ∀ (g : Variety.Point G) (x : Point C.toGeometric),
      ∃ y : Point C.toGeometric, C.inclusion y = A.toMulAction.smul g (C.inclusion x)) :
    Set.range (A.componentAmbientAction C).hom ⊆ Set.range C.inclusion.hom := by
  apply closed_range_of_points
  intro p
  obtain ⟨⟨g, x⟩, rfl⟩ := (prodPointEquiv (ofAffine G) C.toGeometric).symm.surjective p
  change ∃ q, C.inclusion q = A.componentAmbientAction C (prodPoint g x)
  rw [← (affinePointEquiv G).symm_apply_apply g, componentAmbientAction_apply]
  exact hC _ x

private noncomputable def restrictedActionMorphism (A : MorphicAction G V)
    (C : ClosedSubvariety V)
    (hC : ∀ (g : Variety.Point G) (x : Point C.toGeometric),
      ∃ y : Point C.toGeometric, C.inclusion y = A.toMulAction.smul g (C.inclusion x)) :
    Morphism (prod (ofAffine G) C.toGeometric) C.toGeometric :=
  liftClosed C (A.componentAmbientAction C) (A.componentAmbientAction_range C hC)

private theorem restrictedActionMorphism_apply (A : MorphicAction G V)
    (C : ClosedSubvariety V)
    (hC : ∀ (g : Variety.Point G) (x : Point C.toGeometric),
      ∃ y : Point C.toGeometric, C.inclusion y = A.toMulAction.smul g (C.inclusion x))
    (g : Variety.Point G) (x : Point C.toGeometric) :
    C.inclusion (A.restrictedActionMorphism C hC (prodPoint ((affinePointEquiv G).symm g) x)) =
      A.toMulAction.smul g (C.inclusion x) := by
  have h := congrArg (fun f => f (prodPoint ((affinePointEquiv G).symm g) x))
    (liftClosed_fac C (A.componentAmbientAction C) (A.componentAmbientAction_range C hC))
  exact h.trans (A.componentAmbientAction_apply C g x)

private noncomputable def onInvariantClosed (A : MorphicAction G V)
    (C : ClosedSubvariety V)
    (hC : ∀ (g : Variety.Point G) (x : Point C.toGeometric),
      ∃ y : Point C.toGeometric, C.inclusion y = A.toMulAction.smul g (C.inclusion x)) :
    MorphicAction G C.toGeometric where
  smul g x := A.restrictedActionMorphism C hC (prodPoint ((affinePointEquiv G).symm g) x)
  one_smul x := by
    apply inclusion_injective C
    exact (A.restrictedActionMorphism_apply C hC 1 x).trans (A.toMulAction.one_smul _)
  mul_smul g h x := by
    apply inclusion_injective C
    exact (A.restrictedActionMorphism_apply C hC (g * h) x).trans
      ((A.toMulAction.mul_smul g h _).trans
        ((A.restrictedActionMorphism_apply C hC g _).trans
          (congrArg (A.toMulAction.smul g)
            (A.restrictedActionMorphism_apply C hC h x))).symm)
  actionMorphism := A.restrictedActionMorphism C hC
  actionMorphism_apply _ _ := rfl

private theorem onInvariantClosed_smul (A : MorphicAction G V)
    (C : ClosedSubvariety V)
    (hC : ∀ (g : Variety.Point G) (x : Point C.toGeometric),
      ∃ y : Point C.toGeometric, C.inclusion y = A.toMulAction.smul g (C.inclusion x))
    (g : Variety.Point G) (x : Point C.toGeometric) :
    C.inclusion ((A.onInvariantClosed C hC).toMulAction.smul g x) =
      A.toMulAction.smul g (C.inclusion x) :=
  A.restrictedActionMorphism_apply C hC g x


set_option backward.isDefEq.respectTransparency false in
/-- Connected groups preserve each irreducible component of a geometric variety. -/
private theorem translation_component_subset (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V)
    (g : Variety.Point G) : (A.translationMorphism g).hom '' Z.1 ⊆ Z.1 := by
  letI : IrreducibleSpace (ofAffine G).toScheme := ofAffine_isIrreducible_of_isConnected G hG
  letI : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  let U : Set V.toScheme := (⋃₀ (irreducibleComponents V.toScheme \ {Z.1}))ᶜ
  have hUopen : IsOpen U := by
    have h : IsClosed (⋃₀ (irreducibleComponents V.toScheme \ {Z.1})) := by
      rw [Set.sUnion_eq_biUnion]
      exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
    exact h.isOpen_compl
  have hclosure : closure (U ∩ closedPoints V.toScheme) = Z.1 := by
    rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hUopen.isLocallyClosed]
    exact closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents Z.1 Z.2
  have hclosed : IsClosed ((A.translationMorphism g).hom ⁻¹' Z.1) :=
    (isClosed_of_mem_irreducibleComponents Z.1 Z.2).preimage
      (A.translationMorphism g).hom.continuous
  have hsub : U ∩ closedPoints V.toScheme ⊆ (A.translationMorphism g).hom ⁻¹' Z.1 := by
    intro z hz
    let x : Point V := (pointEquivClosedPoint V.structureMap).symm ⟨z, hz.2⟩
    have hx : x.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint V.structureMap).apply_symm_apply ⟨z, hz.2⟩)
    have hirr : _root_.IsIrreducible (Set.range (A.orbitMorphismAt x).hom) := by
      rw [← Set.image_univ]
      exact (IrreducibleSpace.isIrreducible_univ _).image _ (A.orbitMorphismAt x).hom.continuous.continuousOn
    obtain ⟨W, hW, hRW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
    have horbit (a : Variety.Point G) :
        (A.toMulAction.smul a x).1 (IsLocalRing.closedPoint k) ∈ W := by
      apply hRW
      refine ⟨((affinePointEquiv G).symm a).1 (IsLocalRing.closedPoint k), ?_⟩
      exact congrArg (fun p : Point V => p.1 (IsLocalRing.closedPoint k))
        (A.orbitMorphismAt_apply x a)
    have hzW : z ∈ W := by
      have he : A.toMulAction.smul 1 x = x := A.toMulAction.one_smul x
      have ho := horbit 1
      rw [he, hx] at ho
      exact ho
    have hWZ : W = Z.1 := by
      by_contra hne
      exact hz.1 (Set.mem_sUnion.mpr ⟨W, ⟨hW, hne⟩, hzW⟩)
    change (A.translationMorphism g).hom z ∈ Z.1
    rw [← hx, A.translationMorphism_hom_closedPoint, ← hWZ]
    exact horbit g
  have hZsub := closure_minimal hsub hclosed
  rw [hclosure] at hZsub
  rintro _ ⟨z, hz, rfl⟩
  exact hZsub hz

set_option backward.isDefEq.respectTransparency false in
private theorem component_invariant (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V)
    (g : Variety.Point G) (x : Point (irreducibleComponentSubvariety V Z).toGeometric) :
    ∃ y : Point (irreducibleComponentSubvariety V Z).toGeometric,
      (irreducibleComponentSubvariety V Z).inclusion y =
        A.toMulAction.smul g ((irreducibleComponentSubvariety V Z).inclusion x) := by
  apply ((irreducibleComponentSubvariety V Z).inclusion.point_mem_range_iff_closedPoint_mem_range _).mpr
  rw [irreducibleComponentSubvariety_range]
  rw [← A.translationMorphism_hom_closedPoint]
  apply A.translation_component_subset hG Z g
  refine ⟨((irreducibleComponentSubvariety V Z).inclusion x).1 (IsLocalRing.closedPoint k), ?_, rfl⟩
  rw [← irreducibleComponentSubvariety_range V Z]
  exact ⟨x.1 (IsLocalRing.closedPoint k), rfl⟩

private noncomputable def onIrreducibleComponent (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V) :
    MorphicAction G (irreducibleComponentSubvariety V Z).toGeometric :=
  A.onInvariantClosed _ (A.component_invariant hG Z)

private theorem onIrreducibleComponent_smul (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V)
    (g : Variety.Point G) (x : Point (irreducibleComponentSubvariety V Z).toGeometric) :
    (irreducibleComponentSubvariety V Z).inclusion
      ((A.onIrreducibleComponent hG Z).toMulAction.smul g x) =
        A.toMulAction.smul g ((irreducibleComponentSubvariety V Z).inclusion x) :=
  A.onInvariantClosed_smul _ _ g x

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
open BorelGeometricConjugacy Variety.Geometric
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

set_option backward.isDefEq.respectTransparency false in
private theorem centralizer_fixedLocus_invariant
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (g : Variety.Point S.centralizer.carrierVariety)
    (x : Point (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    ∃ y : Point (M.action.subgroupFixedLocus S.toSubgroup).toGeometric,
      (M.action.subgroupFixedLocus S.toSubgroup).inclusion y =
        (M.action.pullbackGroup S.centralizer.inclusion).toMulAction.smul g
          ((M.action.subgroupFixedLocus S.toSubgroup).inclusion x) := by
  obtain ⟨y, hy, -⟩ := (M.action.point_mem_subgroupFixedLocus_iff S.toSubgroup
    (M.action.toMulAction.smul (S.centralizer.inclusion.onPoints g)
      ((M.action.subgroupFixedLocus S.toSubgroup).inclusion x))).mp (by
    intro s
    let a := S.centralizer.inclusion.onPoints g
    have ha : a ∈ S.centralizer.toSubgroup := (S.centralizer.pointEquiv g).property
    have hcomm : (s : Variety.Point H) * a = a * s :=
      (Subgroup.mem_centralizer_iff.mp ha) s s.property
    change M.action.toMulAction.smul (s : Variety.Point H)
      (M.action.toMulAction.smul a ((M.action.subgroupFixedLocus S.toSubgroup).inclusion x)) =
      M.action.toMulAction.smul a ((M.action.subgroupFixedLocus S.toSubgroup).inclusion x)
    let z : Point M.variety := (M.action.subgroupFixedLocus S.toSubgroup).inclusion x
    exact (M.action.toMulAction.mul_smul (s : Variety.Point H) a z).symm.trans
      ((congrArg (fun b => M.action.toMulAction.smul b z) hcomm).trans
        ((M.action.toMulAction.mul_smul a (s : Variety.Point H) z).trans
          (congrArg (M.action.toMulAction.smul a)
            (M.action.subgroupFixedLocus_fixed S.toSubgroup x s)))))
  exact ⟨y, hy⟩

/-- The centralizer acts regularly on the actual reduced fixed locus. -/
public noncomputable def centralizerFixedLocusAction
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H) :
    MorphicAction S.centralizer.carrierVariety
      (M.action.subgroupFixedLocus S.toSubgroup).toGeometric :=
  (M.action.pullbackGroup S.centralizer.inclusion).onInvariantClosed _
    (centralizer_fixedLocus_invariant M S)

/-- The fixed-locus inclusion intertwines the centralizer and ambient actions. -/
public theorem centralizerFixedLocusAction_smul
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (g : Variety.Point S.centralizer.carrierVariety)
    (x : Point (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    (M.action.subgroupFixedLocus S.toSubgroup).inclusion
      ((centralizerFixedLocusAction M S).toMulAction.smul g x) =
        M.action.toMulAction.smul (S.centralizer.inclusion.onPoints g)
          ((M.action.subgroupFixedLocus S.toSubgroup).inclusion x) :=
  (M.action.pullbackGroup S.centralizer.inclusion).onInvariantClosed_smul _ _ g x

/-- A connected centralizer acts regularly on every actual fixed component. -/
public noncomputable def fixedComponentCentralizerAction
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (hC : Variety.IsConnected S.centralizer.carrierVariety)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric) :
    MorphicAction S.centralizer.carrierVariety (fixedComponent M S Z).toGeometric :=
  (centralizerFixedLocusAction M S).onIrreducibleComponent hC Z

set_option backward.isDefEq.respectTransparency false in
/-- The literal fixed-component inclusion is equivariant through the centralizer inclusion. -/
public theorem fixedComponentCentralizerAction_smul
    {B : ClosedSubgroup H} (M : CompleteModel B) (S : ClosedSubgroup H)
    (hC : Variety.IsConnected S.centralizer.carrierVariety)
    (Z : IrreducibleComponent (M.action.subgroupFixedLocus S.toSubgroup).toGeometric)
    (g : Variety.Point S.centralizer.carrierVariety)
    (x : Point (fixedComponent M S Z).toGeometric) :
    (fixedComponent M S Z).inclusion
      ((fixedComponentCentralizerAction M S hC Z).toMulAction.smul g x) =
        M.action.toMulAction.smul (S.centralizer.inclusion.onPoints g)
          ((fixedComponent M S Z).inclusion x) := by
  change (M.action.subgroupFixedLocus S.toSubgroup).inclusion
    ((irreducibleComponentSubvariety _ Z).inclusion
      (((centralizerFixedLocusAction M S).onIrreducibleComponent hC Z).toMulAction.smul g x)) = _
  rw [MorphicAction.onIrreducibleComponent_smul, centralizerFixedLocusAction_smul]
  rfl

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
