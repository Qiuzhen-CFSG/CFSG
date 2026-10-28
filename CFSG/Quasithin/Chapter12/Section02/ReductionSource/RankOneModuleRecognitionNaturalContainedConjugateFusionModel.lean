module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionModel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionReduction

/-!
# Natural-action inputs on the original Chapter 12 layer

Both local contracts are proved for B=[R₂(LT),L], with the original Z_S,
using only genuine 6.1.1, the natural module marking, and E.6.1. The
corank and fusion applications pass these results to the published
consumer deductions. The fusion application uses the already proved
6.1.9 factorization; no new weak-closure or uniqueness premise is added.

The high-parameter application also removes both local callbacks. Its
earlier global bounds, fixed-space alternatives and field-escape premise
remain explicit and belong to the parent source assembly.
Source: Aschbacher--Smith, 6.1.9--11 and 6.1.15, printed pp.669--672.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

theorem source_elementaryActionRankBound
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L)) :
    ElementaryActionRankBound (commutatorLayer T L) n :=
  elementaryActionRankBound_of_natural h611 hnatural hE

theorem source_naturalOffenderFixedLines
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L)) :
    letI := h611.layer_elementary
    NaturalOffenderFixedLines (T : Subgroup G) L (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) :=
  naturalOffenderFixedLines_of_natural h611 hnatural hE

theorem source_conjugateCorankFormula_of_natural_action
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n) :
    ConjugateCorankFormula (T : Subgroup G) (commutatorLayer T L) n :=
  source_conjugateCorankFormula_of_local_rank_bound h611 hnatural hs
    (source_elementaryActionRankBound h611 hnatural hE)

theorem source_mutualConjugateFusion_of_natural_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    MutualConjugateFusion (T : Subgroup G) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) :=
  source_mutualConjugateFusion_of_local_inputs D h h611 hnatural hE hs
    (source_elementaryActionRankBound h611 hnatural hE)
    (source_naturalOffenderFixedLines h611 hnatural hE) hI

theorem source_high_conjugate_centralizes_of_natural_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hfixed : FixedSpaceAlternatives L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hfield : FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  source_high_conjugate_centralizes_of_local_action D h h611 hnatural hE hr hs
    (source_elementaryActionRankBound h611 hnatural hE)
    (source_naturalOffenderFixedLines h611 hnatural hE) hI hfixed hfield hn g hg
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
