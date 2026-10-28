module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Classification.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Classification.BlockKernel

/-!
# The complete small-model comparison of C.1.32

Apply the universally quantified earlier C.1.32 implication to the complete
small MS-pair. Order and unipotent-subgroup comparisons exclude Sp₄(4)
and all nonbinary SL₃ fields. The faithful short-block kernel argument
transfers the A-hat₆ alternative to the actual star group and contradicts
the precise earlier 15.3.27(3). The remaining alternatives are the genuine
A₆ block, G₂(2) block, and an actual binary SL₃ core-quotient equivalence.
Their centers and inherited quasisimplicity give simplicity of L/O₂(L).

`classification_of_source` constructs the MS-pair and proves the required
star-cover exclusion from the genuine earlier local facts. C.1.32 itself
remains the authorized universal earlier input `EarlierMSClassifications`;
no excluded branch or simplicity assumption is added. The parent owns
the subsequent C.1.34 specialization and the V₂ constituent marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.30–34,
printed pp.135–137; 15.3.26–31, pp.1130–1132, especially the first paragraph
of the proof of 15.3.31 on p.1132 (PDF p.1149).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G]

/-- Compare every outcome of the full earlier C.1.32 implication. The
extra exclusion is exactly the source assertion about L*, not a block exclusion. -/
theorem coreAlternatives_of_classification [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierMSClassifications κ)
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hf : HasCharacteristicTwo I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal) (hS : Chapter1.IsSylowIn 2 d.S I)
    (h27 : ¬ Parabolics.IsTripleCoverAlternatingSix (d.starImage I c.L))
    (hm : Parabolics.SmallParabolicMarking d I c.L) (hms : SmallMSPair κ c.L d.S) :
    CoreAlternatives c.L d.S := by
  obtain ⟨P, hP⟩ := hS
  have ha := earlier.rankTwo G c.L d.S hms
  change (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ∨ _ at ha
  rcases ha with h | h | h | h | ⟨n, hn, F, hField, hFinite, hF, ⟨e⟩⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact (not_sp4FourBlock d c hnormal P hP hm h.2).elim
  · exact (not_exceptionalAhat6Block d c hf hYL hnormal ⟨P, hP⟩ h27 h.2).elim
  · exact Or.inr (Or.inr (linearThree_binary d c hnormal P hP hm n hn F hF e).2)

/-- The required block/linear trichotomy and simple core quotient, from
the genuine local source hypotheses and authorized earlier classifications. -/
theorem classification_of_source [Finite G] {κ : GroupClass.{u}}
    (earlier : EarlierMSClassifications κ)
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I) (hSQTK : IsSQTK κ I)
    (hf : HasCharacteristicTwo I) (hYL : d.Yplus ≤ c.L)
    (hLS : I = c.L ⊔ d.S) (hnormal : (c.L.subgroupOf I).Normal)
    (hS : Chapter1.IsSylowIn 2 d.S I)
    (h29 : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
      ¬ ((C.map d.S.subtype).subgroupOf I).Normal)
    (hfacts : Parabolics.RankOneFacts d I) (hcontrol : SolvableInvariantControl d I)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    CoreAlternatives c.L d.S ∧ IsSimpleGroup (c.L ⧸ pCore 2 c.L) := by
  have hms := smallMSPair_of_source d c hSQTK hf hLS hnormal hS h29 hm
  have h27 := Parabolics.not_tripleCoverAlternatingSix d hI c hfacts hcontrol hnormal
  have ha := coreAlternatives_of_classification earlier d c hf hYL hnormal hS h27 hm hms
  exact ⟨ha, coreAlternatives_simple c.core_quotient_quasisimple ha⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

end
