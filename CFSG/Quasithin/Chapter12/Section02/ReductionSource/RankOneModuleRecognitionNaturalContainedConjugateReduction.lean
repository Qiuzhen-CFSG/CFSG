module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateReduction

/-!
# Conjugate geometry on the original Chapter 12 reduced layer

Apply the Chapter 6 assembly to B = [R₂(LT),L] and M = N_G(L).
Its pointwise conclusion is exactly the conjugate-geometry premise of
`source_contained_natural_of_weak_closure_and_conjugate_geometry`.
The second application combines it with the existing normalizer-escape
reduction, proving N_G(W₀(T,B)) ≤ M when n > 2.

The four geometric inputs remain explicit: 6.1.10(3), 6.1.11, the local
fixed-space classification for 6.1.13, and the field escape in 6.1.14(5).
Their independent producers must be discharged before this proves the
requested high-parameter conjugate centralization under source hypotheses.
Source: Aschbacher--Smith, 6.1.15, printed p.672, and 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The pointwise input consumed by the contained-branch assembly,
conditional only on the remaining earlier-source geometric families. -/
theorem source_high_conjugate_centralizes_of_source_inputs
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
    (hfixed : FixedSpaceAlternatives L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hfield : FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) :=
  conjugate_layer_centralizes_of_source_geometry h611 hnatural hE hr hI
    hcorank hfusion hfixed hfield hn g hg

/-- Apply the pointwise theorem to the actual whole-layer weak closure.
The earlier normalizer reduction supplies the noncentralizing conjugate
if this bound fails. This does not assume the 6.1.12(1) disjunction. -/
theorem source_normalizer_W_zero_le_of_conjugate_source_inputs
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
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
    (hfixed : FixedSpaceAlternatives L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hfield : FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hn : 2 < n) :
    normalizer (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G) := by
  by_contra hescape
  obtain ⟨g, _, hg, hnon⟩ :=
    source_noncentralizing_conjugate_of_normalizer_escape D h h611 hnatural hescape
  exact hnon (source_high_conjugate_centralizes_of_source_inputs
    h611 hnatural hE hr hI hcorank hfusion hfixed hfield hn g hg)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
