module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Model
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Generators
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Relations

/-!
# The actual third local model marking

The exact five-relator presentation maps onto both the literal third local
subgroup and the canonical cubic normalizer. The checked presentation bound,
independent literal model witnesses, and canonical pair generation make these
maps isomorphisms. Their composite retains the two original generators.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup ModelCoordinates

private theorem modelPair_satisfies : Coordinates.Nine.Presentation.Satisfies (modelGenerator 4) (modelGenerator 5) :=
  Coordinates.Nine.Presentation.satisfies_of_universal modelGenerator_satisfies

private def toThird : Coordinates.Nine.Presentation.Carrier →* thirdLocalModel :=
  (MulEquiv.subgroupCongr (Coordinates.Nine.Presentation.evaluation_range modelPair_satisfies)).toMonoidHom.comp
    (Coordinates.Nine.Presentation.evaluation modelPair_satisfies).rangeRestrict

private theorem toThird_surjective : Function.Surjective toThird :=
  (MulEquiv.subgroupCongr (Coordinates.Nine.Presentation.evaluation_range modelPair_satisfies)).surjective.comp
    (Coordinates.Nine.Presentation.evaluation modelPair_satisfies).rangeRestrict_surjective

private instance : Finite Coordinates.Nine.Presentation.Carrier := Coordinates.Nine.Presentation.finite_card.1

private theorem presentation_card : Nat.card Coordinates.Nine.Presentation.Carrier = 2160 := by
  apply le_antisymm Coordinates.Nine.Presentation.finite_card.2
  exact thirdLocalModel_card_lower.trans (Nat.card_le_card_of_surjective toThird toThird_surjective)

/-- The literal third local subgroup has order 2160. -/
theorem thirdLocalModel_card : Nat.card thirdLocalModel = 2160 := by
  apply le_antisymm _ thirdLocalModel_card_lower
  exact (Nat.card_le_card_of_surjective toThird toThird_surjective).trans Coordinates.Nine.Presentation.finite_card.2

private def equivOfSurjectiveCard {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hc : Nat.card A = Nat.card B) : A ≃* B :=
  MulEquiv.ofBijective f (by
    let := Fintype.ofFinite A
    let := Fintype.ofFinite B
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    exact ⟨hf,by simpa only [Nat.card_eq_fintype_card] using hc⟩)

private def presentationThirdEquiv : Coordinates.Nine.Presentation.Carrier ≃* thirdLocalModel :=
  equivOfSurjectiveCard toThird toThird_surjective (presentation_card.trans thirdLocalModel_card.symm)

private theorem canonical_evaluation_surjective : Function.Surjective (Coordinates.Nine.Presentation.evaluation canonical_satisfies) := by
  apply MonoidHom.range_eq_top.mp
  rw [Coordinates.Nine.Presentation.evaluation_range,canonical_generates]

private def presentationCanonicalEquiv : Coordinates.Nine.Presentation.Carrier ≃* Canonical :=
  equivOfSurjectiveCard (Coordinates.Nine.Presentation.evaluation canonical_satisfies) canonical_evaluation_surjective
    (presentation_card.trans SourceRecognition.CubicNormalizerModel.model_card.symm)

/-- Exact canonical coordinates for the literal third local subgroup of J₃. -/
def thirdLocalEquiv : thirdLocalModel ≃* Canonical :=
  presentationThirdEquiv.symm.trans presentationCanonicalEquiv

/-- The first original generator retains its explicit canonical coordinate. -/
theorem thirdLocalEquiv_first : thirdLocalEquiv
    ⟨modelGenerator 4,subset_closure (Set.mem_insert _ _)⟩ = canonicalFirst := by
  have he : presentationThirdEquiv Coordinates.Nine.Presentation.a = ⟨modelGenerator 4,subset_closure (Set.mem_insert _ _)⟩ := by
    apply Subtype.ext
    exact Coordinates.Nine.Presentation.evaluation_a modelPair_satisfies
  rw [←he]
  change presentationCanonicalEquiv (presentationThirdEquiv.symm (presentationThirdEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact Coordinates.Nine.Presentation.evaluation_a canonical_satisfies

/-- The second original generator retains its explicit canonical coordinate. -/
theorem thirdLocalEquiv_second : thirdLocalEquiv
    ⟨modelGenerator 5,subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ = canonicalSecond := by
  have he : presentationThirdEquiv Coordinates.Nine.Presentation.z =
      ⟨modelGenerator 5,subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ := by
    apply Subtype.ext
    exact Coordinates.Nine.Presentation.evaluation_z modelPair_satisfies
  rw [←he]
  change presentationCanonicalEquiv (presentationThirdEquiv.symm (presentationThirdEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact Coordinates.Nine.Presentation.evaluation_z canonical_satisfies

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
