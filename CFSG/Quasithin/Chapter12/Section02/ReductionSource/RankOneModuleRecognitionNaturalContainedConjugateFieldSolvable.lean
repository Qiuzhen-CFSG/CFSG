module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldSolvable
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFusionComplete
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFixedSpaces
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosureFixedSpace

/-!
# The solvable central-line action on the original Chapter 12 layer

The natural marking proves solvability of the literal Aut_M(Z_S), discharging
that premise in the field-escape consumer. Combining the checked corank,
fusion, fixed-space and A₂ inputs leaves only the global-s equality and the
field local-component construction in the contained-branch assembly.

Those two remaining source families belong to the consolidated owner
`qt-d-1222-rankone-recognition-natural-contained`. The conditional results
below do not assert that 6.1.14(5) or 6.1.15 has been completed.
Source: Aschbacher--Smith, 6.1.10--15, printed pp.670--672.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The exact normalizer action used in the final contradiction of 6.1.14(5). -/
theorem source_central_line_action_solvable
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    Group.IsSolvable (normalizerAction (normalizer (L : Set G))
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))).range :=
  natural_ZS_normalizerAction_solvable h611 hnatural

/-- The field-escape consumer with both normalizer control and solvability
discharged. The local-component construction remains with this task's owner. -/
theorem source_fieldConjugateEscape_of_fieldNaturalLocalAction
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n) :
    FieldConjugateEscape L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n :=
  source_fieldConjugateEscape_of_local_action D h h611
    (source_central_line_action_solvable h611 hnatural) hloc

/-- All local action inputs are discharged in the high-parameter geometry;
only the global rank and field local-component arguments remain explicit. -/
theorem source_high_conjugate_centralizes_of_rank_and_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G))
    (hn : 2 < n) (g : G)
    (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G) := by
  let := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hr : (n : ℕ∞) ≤ ChapterE.globalR (commutatorLayer T L) := by
    rw [← hs]
    exact ChapterE.globalS_le_globalR _
  exact source_high_conjugate_centralizes_of_corank_fusion_field h611 hnatural hE hr hI
    (source_conjugateCorankFormula_of_natural_action h611 hnatural hE hs)
    (source_mutualConjugateFusion_of_natural_action D h h611 hnatural hE hs hI)
    (source_fieldConjugateEscape_of_fieldNaturalLocalAction D h h611 hnatural hloc) hn g hg

/-- The contained branch with only its remaining rank and field-component
source obligations explicit; no corank, fusion, fixed-space or solvability
callback remains. -/
theorem source_contained_natural_of_rank_and_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n := by
  obtain ⟨hsplit,hhigh,_⟩ := source_natural_weak_closure_of_globalS_eq h611 hnatural hout hs
  exact source_contained_natural_of_weak_closure_and_conjugate_geometry D h h611 hnatural hI
    hsplit hhigh (source_high_conjugate_centralizes_of_rank_and_field_action
      D h h611 hnatural hs hloc hI)

/-- Actual application to the natural-reduction consumer. The independent
escaping-centralizer source branch remains with its existing producer. -/
theorem source_natural_reduction_of_rank_and_field_action
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hCT : (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hloc : FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n)
    (hescape : letI := h611.ZS_normal_in_escape_U
      ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
        normalizer (L : Set G) →
      EscapingAlternative (T : Subgroup G) L (wholeReduced T L) n) :
    Chapter6.Source.Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_natural_reduction_of_source_branches h611 hnatural hCT
    (source_contained_natural_of_rank_and_field_action D h h611 hnatural hout hs hloc) hescape

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
