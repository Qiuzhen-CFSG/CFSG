module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpaces

/-!
# Fixed-space classification on the original Chapter 12 layer

Apply the proved local classification of 6.1.13 to the literal layer
[R₂(LT),L] and M = N_G(L). The second theorem supplies that result to the
existing high-parameter conjugate-centralization consumer, removing its
fixed-space premise. The separate corank, fusion and field-escape inputs
remain with their source producers and the conjugate-geometry assembly.

The ambient setup of 12.2.2(3d) supplies more hypotheses than this local
calculation needs; only its genuine 6.1.1, natural-module and E.6.1 inputs
are retained here. No later recognition result is used.
Source: Aschbacher--Smith, printed pp.670 and 795 (PDF pp.687 and 812).
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ}

/-- The exact fixed-space contract on the original whole reduced layer. -/
theorem source_fixedSpaceAlternatives
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L)) :
    FixedSpaceAlternatives L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n :=
  fixedSpaceAlternatives_of_natural h611 hnatural hE

/-- Discharge the local 6.1.13 input in the actual high-parameter consumer.
The three other geometric families remain independent source obligations. -/
theorem source_high_conjugate_centralizes_of_corank_fusion_field
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L))
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hcorank : ConjugateCorankFormula (T : Subgroup G) (commutatorLayer T L) n)
    (hfusion : MutualConjugateFusion (T : Subgroup G) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)))
    (hfield : FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  source_high_conjugate_centralizes_of_source_inputs h611 hnatural hE hr hI
    hcorank hfusion (source_fixedSpaceAlternatives h611 hnatural hE) hfield hn g hg

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
