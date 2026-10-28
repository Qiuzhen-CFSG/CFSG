module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocal
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionContaining
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalUniqueness

/-!
# The aligned source selection in the Chapter 12 consumer

The simultaneous maximal choices, genuine full-module C.2.8 setup, Sylow
promotion and normal containing component are supplied by the original
Chapter 4 arguments. Only the selected component's quasisimple core quotient
and full ambient normalizer remain explicit here, together with the three
independent source exclusions and the independent right-factor construction.
This conditional adapter does not assert original 4.3.2.

Source: Aschbacher–Smith 4.3.2–5, pp.613–614, and 12.2, p.795.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal Chapter 12 application of the aligned configuration constructor. -/
theorem rankOne_global_preparation_of_component_identifications
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hidentify : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      K.IsCComponent → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      IsQuasisimple (K ⧸ pCore 2 K) ∧ c.H = normalizer (K.map c.H.subtype : Set G))
    (hordinary : ∀ c : SourceConfiguration T L, IsComponent c.H c.K → False)
    (hblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ChapterC.IsBlock c.K → False)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_source_exclusions h hmany hn hpsl hH hgen hN
    (exists_sourceConfiguration_of_component_identifications D h hpsl hidentify)
    hordinary hblock hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
