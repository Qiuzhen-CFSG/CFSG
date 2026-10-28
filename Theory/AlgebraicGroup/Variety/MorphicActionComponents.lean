module

public import Theory.AlgebraicGroup.Variety.MorphicActionPullback
public import Theory.AlgebraicGroup.Variety.GeometricComponents
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.ClosedOrbit
public import Theory.AlgebraicGroup.Bor1.MorphicActionSchemeLaws
public import Theory.AlgebraicGroup.Variety.AffineGroupScheme
/-!
# Connected group actions on irreducible components

A connected group preserves each irreducible component: an orbit through the
open locus belonging to just one component stays there, and closed-point
density extends preservation to the whole component. The action then factors
through the actual reduced closed component.

A positive-dimensional geometric variety has a component with two distinct
rational points. Otherwise finitely many components would give finitely many
closed points, forcing the Jacobson topology to be discrete and dimension zero.
These facts supply the component step in Borel, §13.5.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace Theory.AlgebraicGroup.Variety.Geometric
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {V : Geometric k}
/-- The reduced carrier of a selected irreducible component. -/
@[expose] def reducedIrreducibleComponent (X : Geometric k) (Z : IrreducibleComponent X) :
    ClosedSubvariety X :=
  reducedClosedSubvariety X ⟨Z.1,isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩

omit [IsAlgClosed k] in
@[simp] theorem reducedIrreducibleComponent_range (X : Geometric k)
    (Z : IrreducibleComponent X) :
    Set.range (reducedIrreducibleComponent X Z).inclusion.hom = Z.1 :=
  reducedClosedSubvariety_range X _

instance reducedIrreducibleComponent_irreducibleSpace (X : Geometric k)
    (Z : IrreducibleComponent X) :
    IrreducibleSpace (reducedIrreducibleComponent X Z).toGeometric.toScheme := by
  let C := reducedIrreducibleComponent X Z
  let e₁ := C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
  let e₂ : Set.range C.inclusion.hom ≃ₜ Z.1 :=
    Homeomorph.setCongr (reducedIrreducibleComponent_range X Z)
  exact ((e₁.trans e₂).irreducibleSpace_iff).mpr (Subtype.irreducibleSpace Z.2.1)

namespace MorphicAction
set_option backward.isDefEq.respectTransparency false in
/-- Connected groups preserve each irreducible component of a geometric variety. -/
theorem translation_irreducibleComponent_subset (A : MorphicAction G V)
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

noncomputable def onConnectedGroupComponent (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V) :
    MorphicAction G (reducedIrreducibleComponent V Z).toGeometric :=
  A.onInvariantReducedClosedSubvariety
    ⟨Z.1,isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩ (by
      intro g p hp
      rw [←A.translationMorphism_hom_closedPoint]
      exact A.translation_irreducibleComponent_subset hG Z g ⟨_,hp,rfl⟩)

theorem onConnectedGroupComponent_inclusion (A : MorphicAction G V)
    (hG : Variety.IsConnected G) (Z : IrreducibleComponent V)
    (g : Variety.Point G) (x : Point (reducedIrreducibleComponent V Z).toGeometric) :
    (reducedIrreducibleComponent V Z).inclusion
      ((A.onConnectedGroupComponent hG Z).toMulAction.smul g x) =
        A.toMulAction.smul g ((reducedIrreducibleComponent V Z).inclusion x) :=
  A.onInvariantReducedClosedSubvariety_inclusion _ _ g x
end MorphicAction

theorem exists_component_distinct_points (X : Geometric k) (hdim : ¬ dimension X ≤ 0) :
    ∃ (Z : IrreducibleComponent X)
      (x y : Point (reducedIrreducibleComponent X Z).toGeometric), x ≠ y := by
  classical
  by_contra! h
  letI : ∀ Z : IrreducibleComponent X,
      Subsingleton (Point (reducedIrreducibleComponent X Z).toGeometric) := fun Z => ⟨h Z⟩
  let P := Σ Z : IrreducibleComponent X,
    Point (reducedIrreducibleComponent X Z).toGeometric
  let f : P → Point X := fun p => (reducedIrreducibleComponent X p.1).inclusion p.2
  have hf : Function.Surjective f := by
    intro x
    let z := x.1 (IsLocalRing.closedPoint k)
    let Z : IrreducibleComponent X :=
      ⟨irreducibleComponent z,irreducibleComponent_mem_irreducibleComponents z⟩
    have hz : z ∈ Set.range (reducedIrreducibleComponent X Z).inclusion.hom := by
      rw [reducedIrreducibleComponent_range]
      exact mem_irreducibleComponent
    obtain ⟨y,hy⟩ :=
      ((reducedIrreducibleComponent X Z).inclusion.point_mem_range_iff_closedPoint_mem_range x).mpr hz
    exact ⟨⟨Z,y⟩,hy⟩
  letI : Finite (Point X) := Finite.of_surjective f hf
  letI : Finite (closedPoints X.toScheme) :=
    Finite.of_equiv (Point X) (pointEquivClosedPoint X.structureMap)
  letI : JacobsonSpace X.toScheme := LocallyOfFiniteType.jacobsonSpace X.structureMap
  letI : DiscreteTopology X.toScheme :=
    JacobsonSpace.discreteTopology (Set.finite_coe_iff.mp inferInstance)
  exact hdim (topologicalKrullDim_zero_of_discreteTopology X.toScheme)
end Theory.AlgebraicGroup.Variety.Geometric
