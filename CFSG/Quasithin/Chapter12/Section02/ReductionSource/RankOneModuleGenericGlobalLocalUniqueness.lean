module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocal
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration

/-!
# Applying the remaining original 4.3.2 branches to local preparation

The four explicit obligations are the simultaneous source configuration,
the ordinary-component exclusion (4.3.6), the block exclusion (4.3.7),
and the remaining constrained-component contradiction (4.3.8–16). Their conditional assembly gives exactly uniqueness
over the original L required by local preparation. The independent right
factor remains explicit. This adapter does not claim those obligations are
proved; their final discharge belongs to the rank-one uniqueness owner.

Source: Aschbacher–Smith 4.3.2, pp.613–618; 12.2, p.795.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal consumer with the four earlier-source obligations still explicit.
It becomes the unconditional uniqueness adapter only after all four producers
are supplied; the right-factor construction is independent. -/
theorem rankOne_global_preparation_of_source_exclusions
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hselect : ¬ Chapter4.UniqueMaximalOvergroup L (normalizer (L : Set G)) →
      Nonempty (SourceConfiguration T L))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_rightFactor h hmany hn hpsl hH hgen hN
    (uniqueness_of_source_exclusions hselect hordinary hblock hnonblock) hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
