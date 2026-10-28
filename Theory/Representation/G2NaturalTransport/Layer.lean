module

public import Theory.Representation.G2NaturalTransport.Quotient
public import Theory.SpecificGroups.G2.InvolutoryTwoComponents
public import Theory.GroupTheory.GeneralizedFitting.LayerImages

/-!
# Restricting a full G₂ marking to the literal layer

The actual derived G₂ group is quasisimple, including at field order two.
It is therefore contained in the layer; conversely every component is
perfect and hence lies in the derived subgroup. Transport of components
through an isomorphism identifies the layer of an arbitrary marked L.

We retain the inclusion of E(L) in the original ambient group and prove
that its derived-model equivalence commutes with the full L-marking.
Consequently the source natural-module hypothesis constructs all the
markings used by the quotient transport, with no extra component-model
premise. Source: the distinction between L and E(L) in Aschbacher--Smith
B.4.6, p.88; the I.2.3 natural-module interface, p.413.
-/

@[expose] public section

namespace Atlas.G2.Natural.Transport
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Atlas.G2.Natural
noncomputable section
variable {F G V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal image in G of the layer of L. -/
abbrev layerIn (L : Subgroup G) : Subgroup G := (componentLayer L).map L.subtype

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem model_layer : componentLayer (Atlas.G2.Model F) = commutator (Atlas.G2.Model F) := by
  apply le_antisymm
  · apply sSup_le
    intro K hK
    let := hK.2
    exact (Subgroup.isPerfect_iff.mp (inferInstance : Group.IsPerfect K)).symm.le.trans
      (commutator_mono le_top le_top)
  · exact le_sSup ⟨(inferInstance : (commutator (Atlas.G2.Model F)).Normal).isSubnormal,
      Atlas.G2.InvolutoryTwoComponents.commutator_quasisimple F⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
private theorem layer_map (L : Subgroup G) (e : L ≃* Atlas.G2.Model F) :
    (componentLayer L).map e.toMonoidHom = commutator (Atlas.G2.Model F) := by
  rw [← model_layer]
  apply le_antisymm (map_componentLayer_le e.toMonoidHom e.surjective)
  have hh := Subgroup.map_mono (f := e.toMonoidHom)
    (map_componentLayer_le e.symm.toMonoidHom e.symm.surjective)
  have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro g
    exact e.apply_symm_apply g
  simpa only [Subgroup.map_map, he, Subgroup.map_id] using hh

/-- The full-model marking restricts to the actual layer, including the proper
index-two derived subgroup at q=2. -/
def derivedEquiv (L : Subgroup G) (e : L ≃* Atlas.G2.Model F) :
    layerIn L ≃* commutator (Atlas.G2.Model F) :=
  ((componentLayer L).equivMapOfInjective L.subtype L.subtype_injective).symm.trans
    ((e.subgroupMap (componentLayer L)).trans (MulEquiv.subgroupCongr (by exact layer_map L e)))

/-- The source's full natural-module hypothesis constructs the transport
marking; no separate E(L)-model comparison is an additional premise. -/
def marking (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    (e : L ≃* Atlas.G2.Model F)
    (E : (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] Space F)
    (hE : ∀ l : L, ∀ v, E ((fixedSpace ρ L).mkQ (ρ l v)) =
      action F (e l) (E ((fixedSpace ρ L).mkQ v))) :
    Atlas.G2.Natural.Transport.QuotientMarking (F := F) ρ L (layerIn L) where
  le := by rintro x ⟨l, _, rfl⟩; exact l.property
  full := e
  derived := derivedEquiv L e
  compatible := by
    intro h
    let j := (componentLayer L).equivMapOfInjective L.subtype L.subtype_injective
    change e (j.symm h).val = e ⟨h, _⟩
    have hj : ((j.symm h).val : G) = (h : G) :=
      congrArg (fun z : layerIn L => (z : G)) (j.apply_symm_apply h)
    exact congrArg e (Subtype.ext hj)
  quotient := E
  intertwines := hE

end
end Atlas.G2.Natural.Transport
