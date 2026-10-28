module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanksGlobal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosureRanks

/-!
# Natural-layer ranks and weak closure on the Chapter 12 reduction

The natural module on the original B=[R₂(LT),L] satisfies r(G,B)≥n and
m=s=n. Supplying these ranks to the proved A₂ control gives all three
source 6.1.12 conclusions, with the literal normalizer of W₀ and C₁.
No contained-centralizer hypothesis is used in these rank and closure facts.

The final applications discharge every rank premise in the contained
branch and in its natural-reduction consumer. FieldNaturalLocalAction
remains an explicit source obligation of the consolidated owner
qt-d-1222-rankone-recognition-natural-contained; these conditional applications
do not complete 6.1.14(5) or 6.1.15. The independent escaping branch remains
with the natural-reduction assembly owner.

Source: Aschbacher--Smith, 6.1.10--15, printed pp.670--672.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original natural layer has r≥n and local m=s=n. -/
theorem source_natural_layer_rank_bounds
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    letI := h611.layer_elementary
    (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L) ∧
      ChapterE.localM (commutatorLayer T L) = n ∧
        ChapterE.globalS (commutatorLayer T L) = n :=
  natural_layer_rank_bounds h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)

/-- All three weak-closure conclusions of source 6.1.12 on the original layer. -/
theorem source_natural_weak_closure
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G))) :
    (¬ normalizer (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G)) ∧
    (2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1) ∧
    Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  source_natural_weak_closure_of_globalS_eq h611 hnatural hout
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2

/-- The high-parameter conjugate argument, retaining only the field local-action construction. -/
theorem source_high_conjugate_centralizes_of_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  source_high_conjugate_centralizes_of_rank_and_field_action D h h611 hnatural
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2 hloc hI hn g hg

/-- The contained branch with its rank and weak-closure premises discharged. -/
theorem source_contained_natural_of_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_contained_natural_of_rank_and_field_action D h h611 hnatural hout
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2 hloc hI

/-- The actual natural-reduction consumer, conditional on the two remaining source branches. -/
theorem source_natural_reduction_of_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      EscapingAlternative (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_natural_reduction_of_rank_and_field_action D h h611 hnatural hCT hout
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2 hloc hescape

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
