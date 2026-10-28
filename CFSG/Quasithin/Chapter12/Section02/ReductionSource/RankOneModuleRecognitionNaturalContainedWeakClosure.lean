module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedReduction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedWeakClosure

/-!
# Weak-closure source inputs on the whole Chapter 12 layer

The uniqueness theorem over LT discharges the last premise of E.6.1 on
B = [R₂(LT),L], with M = N_G(L). The generation-one theorem and E.3.10
then give 6.1.12 from the two remaining independent inputs: s(G,B) = n
and the natural-module A₂ fixed-space control. Neither input is assumed
to follow from the definition of the natural model.

Source: Aschbacher--Smith, 6.1.7(2), 6.1.10 and 6.1.12, pp.669--670,
applied to the original reduced subgroup in 12.2.2, p.795.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- All of E.6.1 on the original whole reduced layer. No rank bound or
weak-closure assertion is an input. -/
theorem source_natural_layer_hypothesisE61
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n) :
    ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T
      (normalizer (L : Set G)) (commutatorLayer T L) := by
  apply Chapter6.Source.RankOneRecognition.natural_layer_hypothesisE61 h611 hnatural
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      D.sylow_normalizes_component) (le_componentOrbit L T)
  simpa only [he] using hu.normalizer_unique

/-- The E.3.19 disjunction for the actual generation-one source family.
The numerical premise is retained for its independent 6.1.10 producer. -/
theorem source_weak_closure_escape_of_globalS_eq
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n) :
    ¬ normalizer (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G) := by
  apply Chapter6.Source.RankOneRecognition.weak_closure_escape_of_one_lt_globalS h611 hout
  rw [hs]
  exact_mod_cast h611.n_gt_one

/-- All three weak-closure conclusions on the literal B and Z_S. The
rank equality and A₂ control remain separate source obligations. -/
theorem source_weak_closure_of_rank_and_fixedSpace_control
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hs : letI := h611.layer_elementary; ChapterE.globalS (commutatorLayer T L) = n)
    (hcontrol : letI := h611.layer_elementary;
      ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
        ChapterE.inducedAutomizer (commutatorLayer T L) A ∈
          ChapterE.fixedSpaceFamily (ChapterE.automizerRepresentation (commutatorLayer T L)) 2 →
        A ≤ centralizer
          (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    (¬ normalizer (Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) ∨
      ¬ centralizer (Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1 : Set G) ≤
        normalizer (L : Set G)) ∧
    (2 < n → Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) ≤
      Chapter6.Source.C (commutatorLayer T L) (T : Subgroup G) 1) ∧
    Chapter6.Source.W (commutatorLayer T L) (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer
        (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) :=
  ⟨source_weak_closure_escape_of_globalS_eq h611 hout hs,
    Chapter6.Source.RankOneRecognition.weak_closure_bounds_of_fixedSpace_control
      h611 hs hcontrol⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
