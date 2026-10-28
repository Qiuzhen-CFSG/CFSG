module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionNormalizer

/-!
# Corank and fusion deductions on the original Chapter 12 layer

The layer is literally [R₂(LT),L] and M is N_G(L). These applications
replace the two source-geometry callbacks by a local elementary-image
rank bound and natural offender geometry. The normalizer bound for
S = C_T(Z_S) is supplied by the proved 4.3.1 specialization. The two local
model inputs remain explicit pending their independent source construction.

The final application feeds the existing high-parameter centralization
consumer. Its separate fixed-space alternatives and field-escape inputs
remain with their existing producers. No source theorem is claimed from
these conditional deductions alone.
Source: Aschbacher--Smith, 6.1.9--11 and 6.1.15, printed pp.669--672.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The exact corank contract on the original reduced layer. -/
theorem source_conjugateCorankFormula_of_local_rank_bound
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hbound : ElementaryActionRankBound (commutatorLayer T L) n) :
    ConjugateCorankFormula (T : Subgroup G) (commutatorLayer T L) n :=
  conjugateCorankFormula_of_rank_bound h611 hnatural hs hbound

/-- The exact fusion contract, using Frattini on the actual C_T(Z_S). -/
theorem source_mutualConjugateFusion_of_local_inputs
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hbound : ElementaryActionRankBound (commutatorLayer T L) n)
    (hgeometry : letI := h611.layer_elementary;
      NaturalOffenderFixedLines (T : Subgroup G) L (commutatorLayer T L)
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)))
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    MutualConjugateFusion (T : Subgroup G) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) :=
  mutualConjugateFusion_of_local_inputs h611 hnatural hE hs hbound hgeometry
    (source_central_line_normalizer_factorization D h h611 hI)

/-- The actual parent consumer, discharging its corank and fusion callbacks
from the precise local inputs. Fixed-space classification and field escape
are separate earlier-source obligations and remain explicit. -/
theorem source_high_conjugate_centralizes_of_local_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hbound : ElementaryActionRankBound (commutatorLayer T L) n)
    (hgeometry : letI := h611.layer_elementary;
      NaturalOffenderFixedLines (T : Subgroup G) L (commutatorLayer T L)
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)))
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
  source_high_conjugate_centralizes_of_source_inputs h611 hnatural hE hr hI
    (source_conjugateCorankFormula_of_local_rank_bound h611 hnatural hs hbound)
    (source_mutualConjugateFusion_of_local_inputs D h h611 hnatural hE hs hbound hgeometry hI)
    hfixed hfield hn g hg

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
