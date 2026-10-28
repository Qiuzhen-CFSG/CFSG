module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryComplete

/-!
# Global preparation with aligned source selection discharged

Apply the constructed source configuration and completed ordinary/block
exclusions to uniqueness over the original L. The original Chapter 12
preparation consumer retains only the independently owned nonblock exclusion
and right-factor construction. Final discharge remains with the original
uniqueness and preparation owners; this does not assert unconditional 4.3.2.
Source: Aschbacher–Smith 4.3.2–7, pp.613–616, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- The literal preparation application with all local source-selection
premises discharged. The nonblock exclusion and independent right factor
retain their existing final assembly owners. -/
theorem rankOne_global_preparation_of_nonblock_exclusion
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_rightFactor h.toHypothesis1221 hmany hn hpsl hH hgen hN
    (uniqueness_of_nonblock_exclusion D h hmany hn hpsl hnonblock) hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
