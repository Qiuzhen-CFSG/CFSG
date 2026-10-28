module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Graph
public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Simplicity
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.GraphOrder
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.GroupTheory.PerfectHalfOrderImage

/-!
# Group identification from comparison with the exact ATLAS graph

Conjugate the original permutation action through an adjacency-preserving
vertex bijection into the automorphism group of the explicit ATLAS graph.
The checked graph-group bound is twice the checked ATLAS carrier order.
The original group is perfect and has that same order, so uniqueness of a
perfect subgroup of index at most two identifies the two images. The
resulting group isomorphism intertwines the literal permutation actions.

This completes the group-identification step conditional on the actual graph
comparison. Constructing that comparison remains part of Wales's uniqueness
argument (Pacific J. Math. 30 (1969), p.274). No comparison with the distinct
Leech model, and no simplicity or perfectness of the ATLAS carrier, is assumed.
-/

public section
namespace Sporadic.LeechRelated.HS
open MulAction

/-- A comparison with the literal ATLAS adjacency relation identifies the exact carrier. -/
theorem RankThreeData.recognition_of_graph_equiv {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (e : Fin 100 ≃ Fin 100)
    (he : ∀ x y, NormalizerIndex.adjacency (e x) (e y) ↔ h.graph.Adj x y) :
    ∃ f : P ≃* Carrier, ∀ g x, inclusion (f g) (e x) = e (g • x) := by
  let := h.perfect
  let f₀ : P →* Equiv.Perm (Fin 100) := e.permCongrHom.toMonoidHom.comp P.subtype
  have hf₀ : Function.Injective f₀ := e.permCongrHom.injective.comp Subtype.val_injective
  have hmem (g : P) : f₀ g ∈ NormalizerIndex.graphGroup := by
    intro x y
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    change NormalizerIndex.adjacency (e (g • e.symm (e x))) (e (g • e.symm (e y))) ↔ _
    rw [e.symm_apply_apply, e.symm_apply_apply, he, he, h.graph_invariant]
  let f : P →* NormalizerIndex.graphGroup := f₀.codRestrict _ hmem
  let k : Carrier →* NormalizerIndex.graphGroup :=
    Subgroup.inclusion NormalizerIndex.generated_le_graphGroup
  have hf : Function.Injective f := fun _ _ hh => hf₀ (congrArg Subtype.val hh)
  have hk : Function.Injective k := Subgroup.inclusion_injective _
  have heq : k.range = f.range := Theory.GroupTheory.PerfectHalfOrderImage.range_eq k f hk hf
    (NormalizerIndex.card_carrier.trans h.card.symm)
    (by rw [h.card]; exact NormalizerIndex.graphGroup_card_le)
  let E := Theory.GroupTheory.PerfectHalfOrderImage.equivOfRangeEq f k hf hk heq.symm
  refine ⟨E, ?_⟩
  intro g x
  have hh := congrArg (fun a : NormalizerIndex.graphGroup => a.val (e x))
    (Theory.GroupTheory.PerfectHalfOrderImage.equivOfRangeEq_apply f k hf hk heq.symm g)
  change inclusion (E g) (e x) = e (g • e.symm (e x)) at hh
  simpa only [e.symm_apply_apply] using hh
end Sporadic.LeechRelated.HS
