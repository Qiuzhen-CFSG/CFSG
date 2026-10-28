module
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableContainment
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625CurrentInputs

/-!
# Original 14.6.25 with solvable containment discharged

The earlier exchanged-factor family now proves 14.6.18 for the same selected
M. Apply the completed component construction to that containment and the
independent mixed-size theorem. Its literal terminal witness contradicts the
second-parabolic rank bound. The nonabelian reduction retains its genuine
terminal-solvability premise, and the whole-core A6 reconstruction remains
explicit. No replacement of M or universal MS classification is used.

Source: Aschbacher--Smith, 14.6.11--25 and 14.3.16, printed pp.997--1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Final fixed-M assembly from the genuine earlier source families. The
14.6.12 input may use the original non-model and abelian-span hypotheses;
the theorem constructs the 14.6.18 premise needed by the component branch. -/
theorem source_theorem_14_6_25_of_earlier_factors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (ha : AlternatingSixReconstructionInput.{u} KnownSimple.IsKnownSimple)
    (hterminal : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
        Group.IsSolvable F.TerminalHdot)
    (h12 : ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) → SourceExchangedFactorFamily T M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theorem_14_6_25_of_source_inputs hG T hempty hM hu hmany hrank
  · exact source_theoremE_of_nonabelian_of_solvable
      hG T hempty hM hu hmany hrank hterminal
  · intro hcard e hab
    exact source_second_parabolic_rank_three_of_a6_reconstruction
      hG T hempty hM hu hmany hcard e hab ha
  · intro hnot hcard e hab
    exact ComponentCriticalPair.source_terminal_witness_of_mixed_size
      hG T hempty hM hu hmany hcard e hab
      (source_solvable_le_selected_of_earlier_factors
        hG T hempty hM hu hmany hcard e hab (h12 hnot hab) ha) size

end CFSG.Quasithin.Chapter14.Section06
