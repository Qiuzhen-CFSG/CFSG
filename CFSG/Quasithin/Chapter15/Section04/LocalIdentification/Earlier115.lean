module

public import CFSG.Quasithin.Chapter1.SourceInputs
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.Prebranch
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure

/-!
# Earlier 1.1.5 inputs for the Chapter 15 source applications

The first two clauses and the characteristic-two element-centralizer
consequence are unconditional under the original ambient hypotheses.
The ordinary-component clause uses the complete universal A/B/C and local
quasisimple classifier implications. These adapters retain the literal
subgroups and original involution in the existing Chapter 15 interfaces.

The local marked classifier is proved. The complete applications below
retain only the full universal A/B/C implication, whose producer is
`qt-a02-abc-assembly`. No later recognition premise replaces it.
Source: Aschbacher–Smith 1.1.5, pp.501–503; 15.3.33 and 15.4.22.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open CFSG.Quasithin.ChapterA.Section02
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter15.Section04.SourceRecognition.Source
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The exact first clause consumed by the Chapter 15 component argument. -/
theorem earlier115One : Earlier115One κ G :=
  fun _ _ _ _ _ h => h.intersection_characteristicTwo

/-- Both literal ambient clauses consumed by the two-factor prebranch. -/
theorem earlier115OneTwo : LocalSetup.TwoFactors.Prebranch.Lemma115OneTwo κ G :=
  fun _ _ _ _ _ h => ⟨h.intersection_mem_He, h.inverts_oddCore⟩

/-- The full ordinary-component clause with the genuine universal earlier
classification implications exposed. -/
theorem earlier115Three_of_local_classification
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X)
    (hclass : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (α : MulAut L) (P : Sylow 2 L), MarkedInvolution α P →
        IsTheoremCModel (L ⧸ center L) → ModelAction115 L α) :
    Earlier115Three κ G := by
  intro hG H S M z h D hD
  exact Chapter1.lemma_1_1_5_three_of_local_classification hG hABC hclass H S M z h D hD

/-- The exact combined earlier-source input to the proved 15.4.22 theorem. -/
theorem earlier115_of_local_classification
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X)
    (hclass : ∀ (L : Type u) [Group L] [Finite L] [IsQuasisimple L]
      (α : MulAut L) (P : Sylow 2 L), MarkedInvolution α P →
        IsTheoremCModel (L ⧸ center L) → ModelAction115 L α) :
    Earlier115 (G := G) := by
  intro H S M z hz h
  refine ⟨h.intrinsic_centralizer_characteristicTwo, ?_, ?_⟩
  · intro x
    exact Subtype.ext (h.inverts_oddCore x x.property)
  · intro D hD
    exact (Chapter1.lemma_1_1_5_three_of_local_classification hG hABC hclass H S M z h D hD).2.2
/-- The ordinary-component source clause with the marked classifier discharged. -/
theorem earlier115Three
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC κ X) :
    Earlier115Three κ G := by
  intro hG H S M z h D hD
  exact Chapter1.lemma_1_1_5_three_source hG hABC H S M z h D hD

/-- The complete earlier 1.1.5 source package used by 15.4.22, retaining
only the genuine earlier A/B/C implication. -/
theorem earlier115
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hABC : ∀ (X : Type u) [Group X] [Finite X], TheoremsABC KnownSimple.IsKnownSimple X) :
    Earlier115 (G := G) := by
  intro H S M z hz h
  refine ⟨h.intrinsic_centralizer_characteristicTwo, ?_, ?_⟩
  · intro x
    exact Subtype.ext (h.inverts_oddCore x x.property)
  · intro D hD
    exact (Chapter1.lemma_1_1_5_three_source hG hABC H S M z h D hD).2.2

end CFSG.Quasithin.Chapter15.Section04.SourceRecognition.Source
