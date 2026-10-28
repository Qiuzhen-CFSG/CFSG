module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryNormalizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRootConsumer

/-!
# The centerless ordinary remainder in global rank-one preparation

The nontrivial-center ordinary normalizer is now proved. In the centerless
case the actual T ∩ H is Sylow in the full normalizer, and T does not normalize
K. Supplying a nontrivial two-core in the full ambient centralizer finishes the
normalizer equality and hence the aligned source constructor. The completed
ordinary and block exclusions then give uniqueness over the original L,
conditional only on this core input and the independent nonblock exclusion.

The core input and final assembly remain with
`qt-d-1222-rankone-global-uniqueness`. The nonblock exclusion remains with
`qt-d-1222-rankone-uniqueness-nonblock` and its nonbinary source producer;
the right factor has its independent producer. No callback is discharged
merely by stating these conditional consumers.

Source: Aschbacher–Smith 4.3.2–7, pp.613–616, and 12.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The completed ordinary exclusion rules out the nontrivial-center branch
before the general source configuration has been selected. -/
theorem OutsideChoice.ordinary_center_eq_bot
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    center K = ⊥ := by
  by_contra hz
  obtain ⟨d,_,_,hd⟩ := c.exists_ordinary_sourceConfiguration_of_normalizer D
    h.toHypothesis1221 hpsl K ho hLK hout hKN
    (c.ordinary_normalizer_of_center_ne_bot D h.toHypothesis1221 K ho hKN hz)
  exact d.false_of_ordinary D h hn hpsl hd

/-- Uniqueness over the original L from the remaining centerless centralizer-core
input and the independent nonblock source contradiction. -/
theorem uniqueness_of_centerless_centralizer_core_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hcentralizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal → center K = ⊥ →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ c.H)
        (normalizer (K.map c.H.subtype : Set G)) →
      (¬ (T : Subgroup G) ≤ normalizer (K.map c.H.subtype : Set G)) →
      pCore 2 (centralizer (K.map c.H.subtype : Set G)) ≠ ⊥)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False) :
    ∀ X : Subgroup G, IsMaximalTwoLocal X → L ≤ X → X = normalizer (L : Set G) :=
  uniqueness_of_selection_and_nonblock_exclusion D h hmany hn hpsl
    (exists_sourceConfiguration_of_centerless_centralizer_core D h.toHypothesis1221 hpsl hcentralizer)
    hnonblock

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

/-- Literal preparation application of the centerless normalizer reduction.
The independent right-factor construction remains explicit. -/
theorem rankOne_global_preparation_of_centerless_centralizer_core_and_nonblock_exclusion
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hcentralizer : ∀ (c : OutsideChoice T L) (K : Subgroup c.H),
      IsComponent c.H K → L ≤ K.map c.H.subtype →
      ¬ K.map c.H.subtype ≤ normalizer (L : Set G) → K.Normal → center K = ⊥ →
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ c.H)
        (normalizer (K.map c.H.subtype : Set G)) →
      (¬ (T : Subgroup G) ≤ normalizer (K.map c.H.subtype : Set G)) →
      pCore 2 (centralizer (K.map c.H.subtype : Set G)) ≠ ⊥)
    (hnonblock : ∀ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K → ¬ ChapterC.IsBlock c.K → False)
    (hright : ∀ A B : Subgroup G, CartanPair T L H A B →
      ∃ L₂ : Subgroup G, Global.RightFactor T L H A B L₂) :
    ∃ A B L₂ : Subgroup G, Global.Preparation T L H A B L₂ :=
  D.rankOne_global_preparation_of_selection_and_nonblock_exclusion h hmany hn hpsl
    hH hgen hN
    (exists_sourceConfiguration_of_centerless_centralizer_core D h.toHypothesis1221 hpsl hcentralizer)
    hnonblock hright

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
