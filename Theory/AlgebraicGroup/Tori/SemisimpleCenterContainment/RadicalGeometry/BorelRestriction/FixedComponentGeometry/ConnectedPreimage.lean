module

public import Theory.AlgebraicGroup.Tori.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction.FixedComponents
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.OrbitMap
public import Mathlib.Topology.LocalAtTarget

/-!
# Connected inverse images for the model orbit morphism

The Borel basepoint has exactly the prescribed stabilizer, so every rational
fibre of the actual orbit morphism is connected by the stabilizer-fibre
homeomorphisms. Scheme-point surjectivity follows from rational transitivity,
Jacobson density, and local closedness of orbits.

For an open surjection to a Jacobson space, connected fibres over closed points
suffice to make inverse images of connected closed subsets connected: a putative
open separation upstairs gives intersecting open images downstairs, and a closed
point in their intersection contradicts connectedness of its fibre. Apply this
to the literal support supplied by `componentPreimage_range` and transport along
the reduced inclusion's homeomorphism onto its range.

Openness of the orbit morphism remains an explicit premise. The result therefore
isolates the remaining homogeneous-quotient input to Borel, *Linear Algebraic
Groups*, §11.15 (`refs/KGroup/Bor1/Chapter4.tex`). No smoothness or separability of
the orbit morphism is assumed, and only underlying fibre spaces are compared.
-/

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
open Theory.AlgebraicGroup

private theorem connected_of_open_closed_fibers
    {E D : Type*} [TopologicalSpace E] [TopologicalSpace D]
    [JacobsonSpace D] [ConnectedSpace D] (f : E → D)
    (hf : Function.Surjective f) (ho : IsOpenMap f)
    (hF : ∀ d ∈ closedPoints D, IsPreconnected (f ⁻¹' {d})) :
    ConnectedSpace E := by
  apply connectedSpace_iff_univ.mpr
  refine ⟨?_, ?_⟩
  · obtain ⟨d⟩ := (inferInstance : Nonempty D)
    obtain ⟨e, _⟩ := hf d
    exact ⟨e, trivial⟩
  · intro U V hU hV hcover hUn hVn
    have hcoverD : Set.univ ⊆ f '' U ∪ f '' V := by
      intro d _
      obtain ⟨e, rfl⟩ := hf d
      rcases hcover (Set.mem_univ e) with hu | hv
      · exact Or.inl ⟨e, hu, rfl⟩
      · exact Or.inr ⟨e, hv, rfl⟩
    have hUnD : (Set.univ ∩ f '' U).Nonempty := by
      obtain ⟨e, _, he⟩ := hUn
      exact ⟨f e, trivial, e, he, rfl⟩
    have hVnD : (Set.univ ∩ f '' V).Nonempty := by
      obtain ⟨e, _, he⟩ := hVn
      exact ⟨f e, trivial, e, he, rfl⟩
    have hn : (f '' U ∩ f '' V).Nonempty := by
      simpa only [Set.univ_inter] using
        isPreconnected_univ (f '' U) (f '' V) (ho _ hU) (ho _ hV) hcoverD hUnD hVnD
    obtain ⟨d, ⟨⟨e, heU, hed⟩, ⟨e', heV, he'd⟩⟩, hd⟩ :=
      nonempty_inter_closedPoints hn ((ho _ hU).inter (ho _ hV)).isLocallyClosed
    obtain ⟨z, _, hz⟩ := hF d hd U V hU hV
      (fun e _ => hcover (Set.mem_univ e)) ⟨e, hed, heU⟩ ⟨e', he'd, heV⟩
    exact ⟨z, trivial, hz⟩

/-- Closed rational fibres suffice for connected inverse images under an open quotient map
between Jacobson spaces. -/
private theorem connected_preimage_of_open_closed_fibers
    {E D : Type*} [TopologicalSpace E] [TopologicalSpace D]
    [JacobsonSpace D] (f : E → D)
    (hf : Function.Surjective f) (ho : IsOpenMap f)
    (hF : ∀ d ∈ closedPoints D, IsPreconnected (f ⁻¹' {d}))
    {T : Set D} (hT : IsClosed T) (hTc : IsConnected T) :
    IsConnected (f ⁻¹' T) := by
  letI : ConnectedSpace T := Subtype.connectedSpace hTc
  letI : JacobsonSpace T := JacobsonSpace.of_isClosedEmbedding hT.isClosedEmbedding_subtypeVal
  let r := T.restrictPreimage f
  have hrF (d : T) (hd : d ∈ closedPoints T) : IsPreconnected (r ⁻¹' {d}) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    have him : Subtype.val '' (r ⁻¹' {d}) = f ⁻¹' {d.1} := by
      ext e
      constructor
      · rintro ⟨e, he, rfl⟩
        exact congrArg Subtype.val he
      · intro he
        refine ⟨⟨e, ?_⟩, ?_, rfl⟩
        · change f e ∈ T
          rw [show f e = d.1 from he]
          exact d.2
        · exact Subtype.ext he
    rw [him]
    apply hF d.1
    have hcp := hT.isClosedEmbedding_subtypeVal.preimage_closedPoints
    rw [← hcp] at hd
    exact hd
  haveI : ConnectedSpace (f ⁻¹' T) :=
    connected_of_open_closed_fibers r (hf.restrictPreimage T) (ho.restrictPreimage T) hrF
  exact isConnected_iff_connectedSpace.mpr inferInstance

namespace Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
open BorelGeometricConjugacy Variety.Geometric
attribute [local instance] ClosedSubgroup.carrierAlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : Variety k} [AlgebraicGroup H]

private theorem model_stabilizer_eq {B : ClosedSubgroup H} (M : CompleteModel B) :
    M.action.pointStabilizer (modelBasePoint M) = B := by
  apply SetLike.ext
  intro g
  exact (M.action.mem_pointStabilizer _ g).trans (modelBasePoint_stabilizer M g)

omit [IsAlgClosed k] in
private theorem borel_carrier_connected {B : ClosedSubgroup H} (hB : IsBorelSubgroup B) :
    Variety.IsConnected B.carrierVariety := by
  letI : ConnectedSpace {x : Variety.Point H // x ∈ (B : Set (Variety.Point H))} :=
    Subtype.connectedSpace hB.connected
  letI : ConnectedSpace (Variety.Point B.carrierVariety) :=
    (Variety.closedSubvarietyPointHomeomorph B.isZariskiClosed).connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

/-- Every rational fibre of the actual Borel-model orbit morphism is connected. -/
public theorem modelOrbit_closed_fiber_connected {B : ClosedSubgroup H}
    (M : CompleteModel B) (hB : IsBorelSubgroup B) (y : Point M.variety) :
    _root_.IsConnected ((M.action.orbitMorphismAt (modelBasePoint M)).hom ⁻¹'
      {y.1 (IsLocalRing.closedPoint k)}) := by
  obtain ⟨g, rfl⟩ := modelBasePoint_transitive M y
  let K := M.action.pointStabilizer (modelBasePoint M)
  have hK : Variety.IsConnected K.carrierVariety := by
    dsimp [K]
    rw [model_stabilizer_eq]
    exact borel_carrier_connected hB
  letI : ConnectedSpace (ofAffine K.carrierVariety).toScheme :=
    ofAffine_isConnected_of_isConnected K.carrierVariety hK
  let e := (M.action.orbitFiberStabilizerHomeomorph (modelBasePoint M) g).trans
    ((M.action.orbitMorphismAt (modelBasePoint M)).hom.fiberHomeo _)
  exact isConnected_iff_connectedSpace.mpr (e.connectedSpace_iff.mp inferInstance)

/-- Surjectivity of the actual model orbit map on all scheme points. -/
public theorem modelOrbit_surjective {B : ClosedSubgroup H} (M : CompleteModel B) :
    Function.Surjective (M.action.orbitMorphismAt (modelBasePoint M)).hom := by
  let f := M.action.orbitMorphismAt (modelBasePoint M)
  letI : JacobsonSpace M.variety.toScheme :=
    LocallyOfFiniteType.jacobsonSpace M.variety.structureMap
  have hcp : closedPoints M.variety.toScheme ⊆ Set.range f.hom := by
    intro z hz
    let y : Point M.variety := (pointEquivClosedPoint M.variety.structureMap).symm ⟨z, hz⟩
    have hy : y.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint M.variety.structureMap).apply_symm_apply ⟨z, hz⟩)
    obtain ⟨g, hg⟩ := modelBasePoint_transitive M y
    refine ⟨((affinePointEquiv H).symm g).1 (IsLocalRing.closedPoint k), ?_⟩
    have he := congrArg (fun p : Point M.variety => p.1 (IsLocalRing.closedPoint k))
      ((M.action.orbitMorphismAt_apply (modelBasePoint M) g).trans hg)
    exact he.trans hy
  have hd : closure (Set.range f.hom) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← closure_closedPoints]
    exact closure_mono hcp
  have hc : IsClosed (Set.range f.hom)ᶜ := by
    have ho := (M.action.orbitMorphismAt_range_isLocallyClosed (modelBasePoint M)).isOpen_coborder
    change IsOpen (coborder (Set.range f.hom)) at ho
    rw [coborder_eq_union_closure_compl, hd] at ho
    simpa using ho
  intro z
  by_contra hz
  obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints (show (Set.range f.hom)ᶜ.Nonempty from ⟨z, hz⟩)
    hc.isLocallyClosed
  exact hy (hcp hyc)

/-- The reduced inverse image of a connected closed subvariety is connected once
the actual model orbit morphism is open. -/
public theorem componentPreimage_isConnected_of_isOpenMap
    {B : ClosedSubgroup H} (M : CompleteModel B) (hB : IsBorelSubgroup B)
    (X : ClosedSubvariety M.variety) (hX : Variety.Geometric.IsConnected X.toGeometric)
    (hπ : IsOpenMap (M.action.orbitMorphismAt (modelBasePoint M)).hom) :
    Variety.Geometric.IsConnected (componentPreimage M X).toGeometric := by
  let f := (M.action.orbitMorphismAt (modelBasePoint M)).hom
  letI : JacobsonSpace M.variety.toScheme :=
    LocallyOfFiniteType.jacobsonSpace M.variety.structureMap
  have hF (z : M.variety.toScheme) (hz : z ∈ closedPoints M.variety.toScheme) :
      _root_.IsPreconnected (f ⁻¹' {z}) := by
    let y := (pointEquivClosedPoint M.variety.structureMap).symm ⟨z, hz⟩
    have hy : y.1 (IsLocalRing.closedPoint k) = z :=
      congrArg Subtype.val ((pointEquivClosedPoint M.variety.structureMap).apply_symm_apply ⟨z, hz⟩)
    simpa only [hy] using (modelOrbit_closed_fiber_connected M hB y).isPreconnected
  have hT : _root_.IsConnected (Set.range X.inclusion.hom) := by
    letI : ConnectedSpace X.toGeometric.toScheme := hX
    exact isConnected_range X.inclusion.hom.continuous
  have hc := connected_preimage_of_open_closed_fibers f (modelOrbit_surjective M) hπ hF
    X.inclusion.hom.isClosedEmbedding.isClosed_range hT
  let e := (componentPreimage M X).inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph
  have hR : _root_.IsConnected (Set.range (componentPreimage M X).inclusion.hom) := by
    rw [componentPreimage_range]
    exact hc
  letI : ConnectedSpace (Set.range (componentPreimage M X).inclusion.hom) :=
    Subtype.connectedSpace hR
  exact e.connectedSpace_iff.mpr inferInstance

end Theory.AlgebraicGroup.SemisimpleCenterContainment.RadicalGeometry.BorelRestriction
