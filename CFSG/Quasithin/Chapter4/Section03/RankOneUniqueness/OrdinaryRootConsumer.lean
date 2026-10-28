module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootComplete
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAssembly

/-!
# The ordinary-root contradiction in the original uniqueness consumer

The completed ordinary and block exclusions remove those two premises from
uniqueness over the original L and its Chapter 12 preparation application.
The configuration constructor and constrained nonblock exclusion retain their
independent producers and final assembly owner
`qt-d-1222-rankone-global-uniqueness`; the preparation's right factor remains
independent. These conditional consumers do not assert the full 4.3.2 theorem.

Source: Aschbacher–Smith 4.3.2–7, pp.613–616, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Uniqueness with both ordinary and block branches discharged on the original L. -/
theorem uniqueness_of_selection_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_remaining_source_exclusions D h hmany hn hpsl hselect
    (fun c ho => c.false_of_ordinary D h hn hpsl ho) hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal Chapter 12 application with no ordinary or block exclusion premise. -/
theorem rankOne_global_preparation_of_selection_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_remaining_source_exclusions h hmany hn hpsl hH hgen hN
    hselect (fun c ho => c.false_of_ordinary D h hn hpsl ho) hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
