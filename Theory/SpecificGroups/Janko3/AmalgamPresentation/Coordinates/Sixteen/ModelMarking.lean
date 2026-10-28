module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.FirstModel
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.Generators

/-!
# The actual first local model marking

The exact six-relator presentation maps onto both the literal first local
subgroup of the ATLAS model and the canonical sixteen-field extension.
The independently proved order 8160 and the checked local bound make both
maps isomorphisms. Their composite retains the two original generators.
No recognition or order bound for the full amalgam is assumed.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates

private theorem firstRelations {G : Type*} [Group G] (g : Fin 6 → G)
    (h : Satisfies g) : LocalBound.Satisfies (g 0) (g 1) := by
  intro i
  fin_cases i
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 0
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 1
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 2
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 3
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 4
  · simpa only [LocalBound.relator, relatorWord, eval_cons, eval_nil,
      pow_succ, pow_zero, mul_one, one_mul, Bool.false_eq_true, ↓reduceIte, mul_assoc] using h 5

private theorem modelPair_satisfies :
    LocalBound.Satisfies (modelGenerator 0) (modelGenerator 1) :=
  firstRelations modelGenerator modelGenerator_satisfies

private def toFirst : LocalBound.Carrier →* firstLocalModel :=
  (MulEquiv.subgroupCongr (LocalBound.evaluation_range modelPair_satisfies)).toMonoidHom.comp
    (LocalBound.evaluation modelPair_satisfies).rangeRestrict

private theorem toFirst_surjective : Function.Surjective toFirst :=
  (MulEquiv.subgroupCongr (LocalBound.evaluation_range modelPair_satisfies)).surjective.comp
    (LocalBound.evaluation modelPair_satisfies).rangeRestrict_surjective

private instance : Finite LocalBound.Carrier := LocalBound.finite_card.1

private theorem local_card : Nat.card LocalBound.Carrier = 8160 := by
  apply le_antisymm LocalBound.finite_card.2
  rw [←firstLocalModel_card]
  exact Nat.card_le_card_of_surjective toFirst toFirst_surjective

private def equivOfSurjectiveCard {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (hc : Nat.card A = Nat.card B) : A ≃* B :=
  MulEquiv.ofBijective f (by
    let := Fintype.ofFinite A
    let := Fintype.ofFinite B
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
    exact ⟨hf,by simpa only [Nat.card_eq_fintype_card] using hc⟩)

private def presentationFirstEquiv : LocalBound.Carrier ≃* firstLocalModel :=
  equivOfSurjectiveCard toFirst toFirst_surjective (local_card.trans firstLocalModel_card.symm)

private theorem canonical_evaluation_surjective :
    Function.Surjective (LocalBound.evaluation canonical_satisfies) := by
  apply MonoidHom.range_eq_top.mp
  rw [LocalBound.evaluation_range,canonical_generates]

private def presentationCanonicalEquiv : LocalBound.Carrier ≃*
    Theory.PSL2.BinaryFourFieldExtension.Model := by
  have : Finite Theory.PSL2.BinaryFourFieldExtension.Model := Nat.finite_of_card_ne_zero
    (by rw [Theory.PSL2.BinaryFourFieldExtension.model_card]; decide)
  exact equivOfSurjectiveCard (LocalBound.evaluation canonical_satisfies)
    canonical_evaluation_surjective (local_card.trans Theory.PSL2.BinaryFourFieldExtension.model_card.symm)

/-- The literal first local subgroup has the canonical PSL₂(16):2 coordinates. -/
def firstLocalEquiv : firstLocalModel ≃* Theory.PSL2.BinaryFourFieldExtension.Model :=
  presentationFirstEquiv.symm.trans presentationCanonicalEquiv

/-- The first original generator retains its actual canonical coordinate. -/
theorem firstLocalEquiv_first : firstLocalEquiv
    ⟨modelGenerator 0,subset_closure (Set.mem_insert _ _)⟩ = canonicalFirst := by
  have he : presentationFirstEquiv LocalBound.a =
      ⟨modelGenerator 0,subset_closure (Set.mem_insert _ _)⟩ := by
    apply Subtype.ext
    exact LocalBound.evaluation_a modelPair_satisfies
  rw [←he]
  change presentationCanonicalEquiv (presentationFirstEquiv.symm (presentationFirstEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact LocalBound.evaluation_a canonical_satisfies

/-- The second original generator retains its actual canonical coordinate. -/
theorem firstLocalEquiv_second : firstLocalEquiv
    ⟨modelGenerator 1,subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ = canonicalSecond := by
  have he : presentationFirstEquiv LocalBound.z =
      ⟨modelGenerator 1,subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ := by
    apply Subtype.ext
    exact LocalBound.evaluation_z modelPair_satisfies
  rw [←he]
  change presentationCanonicalEquiv (presentationFirstEquiv.symm (presentationFirstEquiv _)) = _
  rw [MulEquiv.symm_apply_apply]
  exact LocalBound.evaluation_z canonical_satisfies

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
