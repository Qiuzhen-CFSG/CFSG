module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryTransportExtras
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryNative
public import Theory.SpecificGroups.Held.SylowNormalSixteen
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldElementaryPureConjugatorData
/-!
# The six exceptional pure Held sixteen-rows

The literal conjugators send each exceptional mask into catalogue row9 or11.
Both existing rows have order16, so containment of the original order16
subgroup is equality. Their normalizers lie in the certified order21504
involution centralizer, ruling out a factor of five.
Source: Aschbacher--Smith 12.7.5, printed p.840.
-/

public section
open Subgroup
namespace Held.OrdinaryElementary
open LocalPairs.SylowGeometry.Calculations
open TwoLocalCandidates.MaximalNormalizerCatalogue
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration
open TwoLocalCandidates.MaximalNormalizerCatalogue.IntrinsicEnumeration.ExtensionChecks
open TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment
open NativeCoverage PureConjugators

private theorem ambient_card_le_sixteen (j : Fin 22) (hj : j = 9 ∨ j = 11) :
    Nat.card (ambient j) ≤ 16 := by
  classical
  rw [ambient, card_map_of_injective representative.subtype_injective]
  let f : (members (some j)).toFinset → entry j := fun m =>
    ⟨normalForm m, (certified_members (some j) _).mpr
      ⟨m, List.mem_toFinset.mp m.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨m, hm, he⟩ := (certified_members (some j) x).mp x.property
    exact ⟨⟨m,List.mem_toFinset.mpr hm⟩,Subtype.ext he⟩
  have hc : Nat.card (members (some j)).toFinset = 16 := by
    rw [Nat.card_eq_finsetCard]
    rcases hj with rfl | rfl <;> decide
  exact (Nat.card_le_card_of_surjective f hf).trans hc.le

private theorem normalizer_nine_eleven_not_five (j : Fin 22) (hj : j = 9 ∨ j = 11) :
    ¬ 5 ∣ Nat.card (normalizer (ambient j : Set He)) := by
  intro h
  have hn : normalizer (ambient j : Set He) ≤ centralizer ({centralWord} : Set He) := by
    rcases hj with rfl | rfl
    · exact rankFour_normalizer_le_centralizer 1 (by decide)
    · exact rankFour_normalizer_le_centralizer 2 (by decide)
  have hd := h.trans (card_dvd_of_le (hn.trans (centralWord_centralizer_le representative_isPGroup)))
  change 5 ∣ Nat.card CentralizerCertificates.UpperBounds.overgroup at hd
  rw [CentralizerCertificates.UpperBounds.overgroup_card] at hd
  norm_num at hd

private theorem not_five_of_map_le (E : Subgroup He) (hE : Nat.card E = 16) (j : Fin 22) (hj : j=9∨j=11)
    (g : He) (hmap : E.map (MulAut.conj g).toMonoidHom ≤ ambient j) :
    ¬ 5 ∣ Nat.card (normalizer (E : Set He)) := by
  have hc : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 16 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hE
  have he : E.map (MulAut.conj g).toMonoidHom = ambient j :=
    eq_of_le_of_card_ge hmap ((ambient_card_le_sixteen j hj).trans hc.ge)
  intro hd
  apply normalizer_nine_eleven_not_five j hj
  rw [←he,normalizer_card_map_conj]
  exact hd
/-- Every exceptional pure sixteen-row has normalizer order prime to five.
The subgroup is the unchanged input; the only finite hypothesis is its exact
membership in one of the six certified masks. -/
theorem pure_exception_not_five (E : Subgroup He) (hE : Nat.card E = 16)
    (j : Fin 34) (hj : j = 13 ∨ j = 14 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27)
    (hmask : ∀ x : E, ∃ v : Fin 192, (candidateMask j).testBit v.val = true ∧
      (native v).val = x.val) : ¬ 5 ∣ Nat.card (normalizer (E : Set He)) := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 6, sourceRow k = j := by
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
  apply not_five_of_map_le E hE (targetRow k) (by fin_cases k <;> decide) (move k)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv, he⟩ := hmask ⟨x, hx⟩
  change (native v).val = x at he
  rw [← he]
  exact moved_native_mem k v (by simpa only [hk] using hv)

end Held.OrdinaryElementary
