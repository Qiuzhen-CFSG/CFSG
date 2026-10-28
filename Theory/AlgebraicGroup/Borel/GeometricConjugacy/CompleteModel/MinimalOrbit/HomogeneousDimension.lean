module
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.Boundary
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.OrbitMap
import all Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.Boundary
import all Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.MinimalOrbit.StabilizerFiber

/-!
# Equidimensional homogeneous geometric varieties

Closed-point transitivity implies that every nonempty open subset has the
full dimension. Indeed, move a closed point of any irreducible component into
the chosen open, then apply the irreducible open-subvariety dimension theorem.
Every finite irreducible chain is contained in such a component.

Consequently all components have the same dimension. Closed-point homogeneity
also supplies irreducible open neighbourhoods at every scheme point, by
translating one irreducible open and using the Jacobson property. Applications
include disconnected affine groups and their actual locally closed orbits.
This is the equidimensionality needed in Borel's §§1.8 and 11.1 arguments
(`refs/KGroup/Bor1/Chapter1.tex` and `Chapter4.tex`). The internal imports share
only the earlier component-chain and affine-translation implementations.
-/

open CategoryTheory TopologicalSpace AlgebraicGeometry Topology
open Theory.AlgebraicGroup.Variety.Geometric
universe u
namespace Theory.AlgebraicGroup.Variety.Geometric
variable {k : Type u} [Field k]

/-- A nonempty open of a closed-point-homogeneous variety has its full dimension. -/
public theorem dimension_eq_nonemptyOpen_of_closedPoint_transitive
    (V : Geometric k)
    (htrans : ∀ a ∈ closedPoints V.toScheme, ∀ b ∈ closedPoints V.toScheme,
      ∃ e : V.toScheme ≃ₜ V.toScheme, e a = b)
    (U : V.toScheme.Opens) (hne : (U : Set V.toScheme).Nonempty) :
    dimension V = topologicalKrullDim U := by
  apply le_antisymm _ (topologicalKrullDim_subspace_le _ _)
  let : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  obtain ⟨b, hbU, hbclosed⟩ := nonempty_inter_closedPoints hne U.2.isLocallyClosed
  change Order.krullDim (IrreducibleCloseds V.toScheme) ≤ _
  refine iSup_le fun p => ?_
  obtain ⟨Z, hZ, hpZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (p.last : Set V.toScheme) p.last.isIrreducible
  let Z' : IrreducibleComponent V := ⟨Z, hZ⟩
  let C := irreducibleComponentSubvariety V Z'
  have hpdim := ltSeries_length_le_component_dimension V p Z' hpZ
  obtain ⟨a, haZ, haclosed⟩ := nonempty_inter_closedPoints hZ.1.nonempty
    (isClosed_of_mem_irreducibleComponents Z hZ).isLocallyClosed
  obtain ⟨e, he⟩ := htrans a haclosed b hbclosed
  have haC : a ∈ Set.range C.inclusion.hom := by
    rw [irreducibleComponentSubvariety_range]
    exact haZ
  obtain ⟨c, hc⟩ := haC
  let CU : C.toGeometric.toScheme.Opens :=
    ⟨(e ∘ C.inclusion.hom) ⁻¹' U, U.2.preimage (e.continuous.comp C.inclusion.hom.continuous)⟩
  have hCU : (CU : Set C.toGeometric.toScheme).Nonempty := by
    refine ⟨c, ?_⟩
    change e (C.inclusion.hom c) ∈ U
    rw [hc, he]
    exact hbU
  have hdim := dimension_eq_nonemptyOpen C.toGeometric CU hCU
  let j : CU → U := fun c => ⟨e (C.inclusion.hom c.1), c.2⟩
  have hj : IsEmbedding j :=
    (e.isEmbedding.comp (C.inclusion.hom.isClosedEmbedding.isEmbedding.comp
      IsEmbedding.subtypeVal)).codRestrict _ _
  exact hpdim.trans (hdim.trans_le hj.isInducing.topologicalKrullDim_le)

/-- All irreducible components of a closed-point-homogeneous variety have equal dimension. -/
public theorem component_dimension_eq_of_closedPoint_transitive
    (V : Geometric k)
    (htrans : ∀ a ∈ closedPoints V.toScheme, ∀ b ∈ closedPoints V.toScheme,
      ∃ e : V.toScheme ≃ₜ V.toScheme, e a = b)
    (Z : IrreducibleComponent V) :
    dimension (irreducibleComponentSubvariety V Z).toGeometric = dimension V := by
  let C := irreducibleComponentSubvariety V Z
  have heq : dimension C.toGeometric = topologicalKrullDim Z.1 := by
    have h := C.inclusion.hom.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
      |>.topologicalKrullDim_eq
    rwa [irreducibleComponentSubvariety_range] at h
  rw [heq]
  apply le_antisymm (topologicalKrullDim_subspace_le _ _)
  obtain ⟨U, hU, hUne, hUZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z.1 Z.2
  change dimension V ≤ topologicalKrullDim Z.1
  rw [V.dimension_eq_nonemptyOpen_of_closedPoint_transitive htrans ⟨U, hU⟩ hUne]
  exact (IsEmbedding.inclusion hUZ).isInducing.topologicalKrullDim_le

/-- Closed-point homogeneity gives irreducible open neighbourhoods at all scheme points. -/
public theorem exists_irreducible_open_nhds_of_closedPoint_transitive
    (V : Geometric k)
    (htrans : ∀ a ∈ closedPoints V.toScheme, ∀ b ∈ closedPoints V.toScheme,
      ∃ e : V.toScheme ≃ₜ V.toScheme, e a = b)
    (z : V.toScheme) :
    ∃ U : V.toScheme.Opens, z ∈ U ∧ _root_.IsIrreducible (U : Set V.toScheme) := by
  let : JacobsonSpace V.toScheme := LocallyOfFiniteType.jacobsonSpace V.structureMap
  let Z := irreducibleComponent z
  have hZ : Z ∈ irreducibleComponents V.toScheme := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨W, hW, hWne, hWZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have hWirr : _root_.IsIrreducible W := ⟨hWne, hZ.1.2.open_subset hW hWZ⟩
  obtain ⟨a, haW, haclosed⟩ := nonempty_inter_closedPoints hWne hW.isLocallyClosed
  let S : Set V.toScheme := {b | ∃ U : Set V.toScheme,
    IsOpen U ∧ _root_.IsIrreducible U ∧ b ∈ U}
  have hS : IsOpen S := by
    apply isOpen_iff_forall_mem_open.mpr
    rintro b ⟨U, hU, hUi, hbU⟩
    exact ⟨U, fun c hc => ⟨U, hU, hUi, hc⟩, hU, hbU⟩
  have hclosed : closedPoints V.toScheme ⊆ S := by
    intro b hb
    obtain ⟨e, he⟩ := htrans a haclosed b hb
    exact ⟨e '' W, e.isOpenMap W hW,
      hWirr.image e e.continuous.continuousOn, ⟨a, haW, he⟩⟩
  have hz : z ∈ S := by
    by_contra hz
    obtain ⟨b, hbSc, hbclosed⟩ :=
      nonempty_inter_closedPoints (show Sᶜ.Nonempty from ⟨z, hz⟩) hS.isClosed_compl.isLocallyClosed
    exact hbSc (hclosed hbclosed)
  obtain ⟨U, hU, hUi, hzU⟩ := hz
  exact ⟨⟨U, hU⟩, hzU, hUi⟩

variable [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
/-- Left translations act transitively on the closed points of an affine group scheme. -/
public theorem ofAffine_group_closedPoint_transitive
    (G : Theory.AlgebraicGroup.Variety k) [AlgebraicGroup G] :
    ∀ a ∈ closedPoints (ofAffine G).toScheme, ∀ b ∈ closedPoints (ofAffine G).toScheme,
      ∃ e : (ofAffine G).toScheme ≃ₜ (ofAffine G).toScheme, e a = b := by
  intro a ha b hb
  let p : Point (ofAffine G) :=
    (pointEquivClosedPoint (ofAffine G).structureMap).symm ⟨a, ha⟩
  let q : Point (ofAffine G) :=
    (pointEquivClosedPoint (ofAffine G).structureMap).symm ⟨b, hb⟩
  have hp : p.1 (IsLocalRing.closedPoint k) = a :=
    congrArg Subtype.val ((pointEquivClosedPoint (ofAffine G).structureMap).apply_symm_apply ⟨a, ha⟩)
  have hq : q.1 (IsLocalRing.closedPoint k) = b :=
    congrArg Subtype.val ((pointEquivClosedPoint (ofAffine G).structureMap).apply_symm_apply ⟨b, hb⟩)
  let g := affinePointEquiv G q * (affinePointEquiv G p)⁻¹
  have hpoint : ofAffine_morphism (leftMulMorphism G g) p = q := by
    apply (affinePointEquiv G).injective
    rw [affinePointEquiv_ofAffine_morphism]
    change g * affinePointEquiv G p = affinePointEquiv G q
    simp [g]
  refine ⟨Scheme.homeoOfIso (affineLeftTranslationIso g), ?_⟩
  rw [← hp, ← hq]
  exact congrArg (fun r : Point (ofAffine G) => r.1 (IsLocalRing.closedPoint k)) hpoint

/-- Every nonempty open in an affine group has the full group dimension. -/
public theorem ofAffine_group_nonemptyOpen_dimension
    (G : Theory.AlgebraicGroup.Variety k) [AlgebraicGroup G]
    (U : (ofAffine G).toScheme.Opens) (hne : (U : Set (ofAffine G).toScheme).Nonempty) :
    topologicalKrullDim U = (Cardinal.toNat (Variety.dimension G) : WithBot ℕ∞) := by
  rw [← dimension_eq_nonemptyOpen_of_closedPoint_transitive (ofAffine G)
    (ofAffine_group_closedPoint_transitive G) U hne]
  exact MinimalOrbit.ofAffine_group_dimension G

namespace MorphicAction
variable {G : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup G]
variable {X : Geometric k} (A : MorphicAction G X) (x : Point X)

/-- Every irreducible component of an orbit has the dimension of the whole orbit. -/
public theorem orbitSubvariety_component_dimension
    (Z : IrreducibleComponent (A.orbitSubvariety x).toGeometric) :
    dimension (irreducibleComponentSubvariety (A.orbitSubvariety x).toGeometric Z).toGeometric =
      dimension (A.orbitSubvariety x).toGeometric :=
  component_dimension_eq_of_closedPoint_transitive _ (A.orbitSubvariety_closedPoint_transitive x) Z

/-- Every nonempty open in an orbit has the dimension of the whole orbit. -/
public theorem orbitSubvariety_nonemptyOpen_dimension
    (U : (A.orbitSubvariety x).toGeometric.toScheme.Opens)
    (hne : (U : Set (A.orbitSubvariety x).toGeometric.toScheme).Nonempty) :
    topologicalKrullDim U = dimension (A.orbitSubvariety x).toGeometric :=
  (dimension_eq_nonemptyOpen_of_closedPoint_transitive _
    (A.orbitSubvariety_closedPoint_transitive x) U hne).symm

/-- Nonempty open pieces of rational scheme fibres have the full stabilizer dimension. -/
public theorem toOrbitSubvariety_fiber_nonemptyOpen_dimension
    (y : Point (A.orbitSubvariety x).toGeometric)
    (U : ((A.toOrbitSubvariety x).hom.fiber (y.1 (IsLocalRing.closedPoint k))).Opens)
    (hne : (U : Set ((A.toOrbitSubvariety x).hom.fiber
      (y.1 (IsLocalRing.closedPoint k)))).Nonempty) :
    topologicalKrullDim U =
      (Cardinal.toNat (Variety.dimension (A.pointStabilizer x).carrierVariety) : WithBot ℕ∞) := by
  let e := A.toOrbitSubvarietyFiberStabilizerHomeomorph x y
  let V : (ofAffine (A.pointStabilizer x).carrierVariety).toScheme.Opens :=
    ⟨e ⁻¹' U, U.2.preimage e.continuous⟩
  have hV : (V : Set (ofAffine (A.pointStabilizer x).carrierVariety).toScheme).Nonempty := by
    obtain ⟨z, hz⟩ := hne
    refine ⟨e.symm z, ?_⟩
    change e (e.symm z) ∈ U
    rw [e.apply_symm_apply]
    exact hz
  have hd := ofAffine_group_nonemptyOpen_dimension (A.pointStabilizer x).carrierVariety V hV
  have heq := (e.isEmbedding.homeomorphImage (V : Set _)).isHomeomorph.topologicalKrullDim_eq
  have himage : e '' (V : Set _) = U := Set.image_preimage_eq _ e.surjective
  rw [himage] at heq
  exact heq.symm.trans hd

end MorphicAction
end Theory.AlgebraicGroup.Variety.Geometric
