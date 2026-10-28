module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoMarkedComparison

/-!
# Oriented restoration of the field-four Hall–Janko comparison

The noncommuting field-four source places its beta endpoint first in the
native J₂ model. Once its two reduced endpoint maps agree on the full Borel,
the original inclusion diagram is therefore the reverse of the usual source
orientation. The original Sylow either equals its reduced subgroup, allowing
literal subgroup transport, or the proved outer-involution reconstruction
gives the full Aut(J₂) diagram. Both alternatives retain the whole Borel and
the two commuting inclusion squares.

The compatible reduced comparison is the sole additional input to this
restoration step. Independent parabolic isomorphisms do not supply it.

Source: DGS, *Groups and Graphs* (1985), (10.9), pp.162–163, and
(15.3), pp.229–231.
-/

public noncomputable section
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.SplitComparison
open GreenBook SuzukiContainment

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Restore the exact field-four source orientation while retaining compatible
maps on the entire original Borel in both the inner and proper outer cases. -/
theorem original_reversed_j2_or_autJ2_iso
    (h : HypothesisF11 L S)
    (e : RankTwoAmalgam.Iso (reducedAmalgam L S).reverse
      HallJanko.j2Model.toMarking.amalgam) :
    Nonempty (RankTwoAmalgam.Iso (originalAmalgam L S).reverse
      HallJanko.j2Model.toMarking.amalgam) ∨
    Nonempty (RankTwoAmalgam.Iso (originalAmalgam L S).reverse
      HallJanko.autJ2Model.toMarking.amalgam) := by
  by_cases hs : S = reducedSylow L S
  · exact Or.inl ⟨(NativeRestoration.originalIsoReduced hs).reverse.trans e⟩
  · obtain ⟨E, _, _, _⟩ := original_autJ2_iso h 1 0 e hs
    exact Or.inr ⟨E⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo.SplitComparison
