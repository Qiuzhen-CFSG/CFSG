module

public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.Common
public import Theory.SpecificGroups.Janko3.Model.ThreeRank.Elementary
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank

/-!
# The sporadic strong-quasithin output list

The genuine ordinary three-ranks of J₃ and McL remove precisely those two
entries from the sporadic Theorem B list, yielding the Theorem C list.

Source: Aschbacher–Smith A.2.19, printed pp.40–41 (Case I and Case II).
-/

namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
open ClassificationModels Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
public theorem theoremC_of_theoremBSporadicModel (hq : IsStronglyQuasithin G)
    (hb : IsTheoremBSporadicModel G) : IsTheoremCModel G := by
  rcases hb with h | h
  · obtain ⟨name,⟨e⟩⟩ := h
    by_cases hj : name = .j3
    · subst name
      change G ≃* _root_.Sporadic.Janko3.Model at e
      have hr := hq 3 (by decide) (by decide)
      rw [primeRank_equiv 3 e] at hr
      exact False.elim (by have hh := _root_.Sporadic.Janko3.j3_primeRank_three_ge; omega)
    · exact .sporadic (Or.inl ⟨name,hj,⟨e⟩⟩)
  · rcases h with h | h
    · exact .sporadic (Or.inr h)
    · obtain ⟨e⟩ := h
      have hr := hq 3 (by decide) (by decide)
      rw [primeRank_equiv 3 e] at hr
      exact False.elim (not_le_of_gt _root_.Sporadic.LeechRelated.McL.two_lt_primeRank_three hr)
end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly
