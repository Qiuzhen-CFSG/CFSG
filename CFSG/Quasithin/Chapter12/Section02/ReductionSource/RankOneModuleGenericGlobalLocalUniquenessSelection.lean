module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionConstrainedQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootConsumer

/-!
# The containing-component quotient in global rank-one preparation

C.2.11 and Fitting-preimage functoriality now supply the quasisimple quotient
of the actual normal component containing L. The aligned constructor therefore
retains only the ordinary full-normalizer identification. The proved ordinary
and block contradictions then leave the independent nonblock exclusion in the
uniqueness theorem over L, and the independent right factor in Chapter 12.

The ordinary normalizer and final source assembly remain with
`qt-d-1222-rankone-global-uniqueness`; the nonblock exclusion remains with
`qt-d-1222-rankone-uniqueness-nonblock`, using its earlier nonbinary input.
These conditional consumers do not assert the completed source theorem.

Source: Aschbacher–Smith 4.3.2–7, pp.613–616, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The constrained quotient and ordinary/block exclusions are discharged;
the ordinary normalizer and source nonblock contradiction remain explicit. -/
theorem uniqueness_of_ordinary_normalizer_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hordinary : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_selection_and_nonblock_exclusion D h hmany hn hpsl
    (exists_sourceConfiguration_of_ordinary_normalizer D h.toHypothesis1221 hpsl hordinary)
    hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal preparation consumer with the constrained quotient supplied by C.2.11. -/
theorem rankOne_global_preparation_of_ordinary_normalizer_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hordinary : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal →
      c.H = normalizer (K.map c.H.subtype : Set G))
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_selection_and_nonblock_exclusion h hmany hn hpsl
    hH hgen hN
    (exists_sourceConfiguration_of_ordinary_normalizer D h.toHypothesis1221 hpsl hordinary)
    hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
