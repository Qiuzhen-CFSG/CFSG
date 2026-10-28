module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognitionInputs
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalAssembly
public import CFSG.Quasithin.ChapterG.Section03.FullRoot

/-!
# Full-action recognition and conditional natural-module assembly

A full axis in the original LT action now forces its faithful image to be
GL(V). The dimension lower bound and intrinsic two-core guard are discharged
from the chosen module and reducedness. This works for the indecomposable
four-dimensional alternative as well as the irreducible alternatives.

The final natural-module assembly retains two independent source obligations:
construct the axis from the solvable conjugate TI pair, and identify the
original L/O₂(L) action with a natural module of dimension three through five
once its full LT image is known. The latter marking is transported using the
original quotient projection. These conditional statements feed naturalStep
in the unchanged local assembly; they do not assert original 12.2.20 before
the two source producers are discharged.

Source: Aschbacher--Smith, the construction preceding 12.2.20 and that lemma,
printed p.802, using corrected G.3.1 with trivial two-core, pp.337--338.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
/-- Recognition of the full literal join image from its one full axis. This
includes the indecomposable alternative of 12.2.2, with no irreducibility input. -/
theorem chosenJoinLinearAction_range_eq_top_of_full_axis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hr : IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))))
    (haxis : ChosenFullAxis D hT) :
    letI := D.elementary
    (chosenJoinLinearAction D hT).range = ⊤ := by
  let := D.elementary
  obtain ⟨f, hf, hfull⟩ := haxis
  exact ChapterG.Section03.eq_top_of_full_axis_of_twoCore_eq_bot
    (chosenJoinLinearAction_twoCore_eq_bot_of_reduced D hT hr)
    (chosen_finrank_ge_three h D) f hf hfull

/-- The same full-action conclusion with the ambient-local structural API. -/
theorem chosenJoinLinearAction_range_eq_top_of_full_axis_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (haxis : ChosenFullAxis D (((structural L h).2.2 V D).1)) :
    letI := D.elementary
    (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤ :=
  chosenJoinLinearAction_range_eq_top_of_full_axis h D _
    (((structural L h).2.2 V D).2.1) haxis

/-- Conditional naturalStep assembly. The two source obligations are separate:
construct a full axis from the solvable TI pair, and identify the original
quotient action after the full join image has been proved. -/
theorem natural_action_of_solvable_axis_and_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2)
    (axisStep : NoEscape L V → ChapterI.Section06To08.IsTISubgroup V →
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) →
      Group.IsSolvable H → ¬ V ≤ H.pCoreIn 2 →
      ChosenFullAxis D (((structural L h).2.2 V D).1))
    (markingStep : (letI := D.elementary
      (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤) →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
        (Representation.specialLinearNatural (k := ZMod 2) d))) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) := by
  have hfull := chosenJoinLinearAction_range_eq_top_of_full_axis_at h D structural
    (axisStep hnone hTI hH hs hm)
  obtain ⟨d, hd, ⟨e⟩⟩ := markingStep hfull
  exact ⟨d, hd, D.conjugationModel_of_quotientAction e⟩

/-- The two independent recognition producers feed the unchanged natural local
assembly, with all H-star existence, rank and solvability inputs retained. -/
theorem naturalLocalAnalysis_of_axis_source_inputs
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hnone : NoEscape L V) (hTI : ChapterI.Section06To08.IsTISubgroup V)
    (hexists : (Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))).Nonempty)
    (rankStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      primeRank 2 (H ⧸ pCore 2 H) ≤ 2)
    (solvableStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      ¬ V ≤ H.pCoreIn 2 → Group.IsSolvable H)
    (axisStep : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Group.IsSolvable H → ¬ V ≤ H.pCoreIn 2 →
      ChosenFullAxis D (((structural G T L h).2.2 V D).1))
    (markingStep : (letI := D.elementary
      (chosenJoinLinearAction D (((structural G T L h).2.2 V D).1)).range = ⊤) →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
        (Representation.specialLinearNatural (k := ZMod 2) d))) :
    ∃ d, NaturalLocalAnalysis T L V d := by
  apply naturalLocalAnalysis_of_source_inputs h D structural hnone hTI
    hexists rankStep solvableStep
  intro H hH hs hm
  exact natural_action_of_solvable_axis_and_marking h D (structural.at T) hnone hTI hH hs hm
    (fun _ _ hH hs hm => axisStep H hH hs hm) markingStep

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
