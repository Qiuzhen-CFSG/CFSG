module
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625OriginalSize
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SourceCompletion

/-!
# Original rank-two classification after terminal solvability

The original terminal components are excluded by the proved J₃ and triality
recognition arguments. The fixed-M classification therefore retains only
the actual alternating-six reconstruction and exchanged-factor family.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original fixed-M endpoint with terminal solvability and the
mixed-size bound supplied internally. -/
theorem source_theorem_14_6_25_after_terminal_completion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (h12 : ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) → SourceExchangedFactorFamily T M) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theorem_14_6_25_of_original_size hG T hempty hM hu hmany hrank ha ?_ h12
  intro hnot F hne g hgP hgH
  obtain ⟨hcard,⟨e⟩⟩ := source_plane_of_rankTwo hrank
  exact TerminalSolvable.source_terminal_solvable hG T hempty hM hu hmany hcard e
    hnot F hne g hgP hgH

end CFSG.Quasithin.Chapter14.Section06
