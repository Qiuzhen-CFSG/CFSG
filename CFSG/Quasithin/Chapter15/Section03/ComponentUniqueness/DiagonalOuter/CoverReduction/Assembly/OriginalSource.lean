module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.SourceBorel.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage.FixedVectors

/-!
# The first paragraph of the original cover reduction

The selected hypotheses construct the literal earlier-source record and
the actual marked local cover. Only the independently owned uniform
source13 exclusion and source37 alternative remain explicit.
Source: Aschbacher--Smith 15.3.38, printed pp.1135--1136.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open ChapterA.Section05To06 LocalCover
variable {G : Type*} [Group G] [Finite G]

theorem source_inputs_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (h37 : ∀ J ∈ d.Hplus, ∀ K : Subgroup G,
      K ≤ J → IsComponent J (K.subgroupOf J) →
      d.Yplus ≤ localSpan K d.S ∨
        3 ^ (Nat.card (centralizingPart d.Yplus K)).factorization 3 = 3 ∨
        Candidates.RankTwoDiagonal d.Yplus K (localSpan K d.S)) : SourceInputs d := by
  have earlier := source_borel_earlier_from_selection hG d hempty hM hu hmany h13 htwo
  obtain ⟨hne,_,_⟩ := InitialSource.UniformControl.source_controls_of_ordering_maximal
    hG d.T hempty hM hu hmany (d.action.card_centralInvolutions d.T d.sylow_le)
  obtain ⟨himage,_,_,_,_,_,h7⟩ :=
    source_lemma_15_3_7_of_orthogonal_action hG d.T hempty d.action hM hu hmany hne
  refine {
    earlier := earlier
    setup := fun J K h => matrix_source_setup_of_earlier d earlier h7 h
    alternatives := h37
    second_choice := ?_
    residual_alternatives := h7
    residual_image := himage
    central_omega := ?_
    fixed_vectors := ?_ }
  · intro hchoice hY
    have hs := (OutsideStructure.source_lemma_15_3_11_from_selection
      hG d hempty hM hu hmany I hI).second_choice ⟨hchoice, hY⟩
    exact ⟨hs.2.1, hs.2.2.1⟩
  · rw [← (source_lemma_15_3_8 d.T d.action d.sylow_le 1).1]
    exact inf_le_left
  · exact d.action.fixedPlane_eq_bot_of_residual_image
      (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc) himage

/-- The first paragraph of source15.3.38 on the actual contrary component. -/
theorem local_result_from_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : CharacteristicTwo.LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (h13 : ∀ J ∈ d.Hplus, generalizedFitting J ≠ pCore 2 J)
    (h37 : ∀ J ∈ d.Hplus, ∀ K : Subgroup G,
      K ≤ J → IsComponent J (K.subgroupOf J) →
      d.Yplus ≤ localSpan K d.S ∨
        3 ^ (Nat.card (centralizingPart d.Yplus K)).factorization 3 = 3 ∨
        Candidates.RankTwoDiagonal d.Yplus K (localSpan K d.S))
    {I L : Subgroup G} (h : SourceBorel.Setup d I L) : Nonempty (LocalResult d I L) := by
  have h11 := OutsideStructure.source_lemma_15_3_11_from_selection
    hG d hempty hM hu hmany I h.outside
  have htwo := ComponentIntersection.rank_two_case_of_three_rank_two
    d I h11.local_structure h.residual_rank
  exact local_result (source_inputs_from_selection hG d hempty hM hu hmany h13 h.outside htwo h37) h

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
