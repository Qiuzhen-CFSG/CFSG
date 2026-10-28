module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosureRanks
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldSolvable

/-!
# The exact local natural-layer rank in Chapter 12

The full automizer of the original layer has minimum involution codimension
n. Thus the remaining global-r bound implies s(G,B)=n and supplies all three
weak-closure conclusions. The contained-branch application combines this
calculation with the checked local action family; its global-r bound and
field local-component construction remain explicit source obligations of
`qt-d-1222-rankone-recognition-natural-contained`.

Source: Aschbacher--Smith, 6.1.10(1--2), 6.1.12 and 6.1.15, pp.670--672.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The local minimum in source 6.1.10(2), on the literal original layer. -/
theorem source_natural_layer_localM_eq
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    letI := h611.layer_elementary; ChapterE.localM (commutatorLayer T L) = n :=
  natural_layer_localM_eq h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)

/-- Only the global-r lower bound remains in source 6.1.10(2). -/
theorem source_natural_globalS_eq_of_globalR_ge
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L)) :
    letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n := by
  let := h611.layer_elementary
  rw [ChapterE.globalS,source_natural_layer_localM_eq D h h611 hnatural]
  exact min_eq_right hr

/-- Apply the exact local minimum and the proved A₂ control to all three
weak-closure conclusions, retaining the independent global-r lower bound. -/
theorem source_natural_weak_closure_of_globalR_ge
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L)) :
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
    (source_natural_globalS_eq_of_globalR_ge D h h611 hnatural hr)

/-- The remaining contained-branch obligations are the global-r estimate
and the field-fixed-space local component construction. -/
theorem source_contained_natural_of_globalR_and_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L))
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_contained_natural_of_rank_and_field_action D h h611 hnatural hout
    (source_natural_globalS_eq_of_globalR_ge D h h611 hnatural hr) hloc hI

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
