module

public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.SourceComplete
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SolvableAssembly

/-!
# The current source-input adapter for original 14.6.25

The final rank-two source theorem consumes three independent source families:
nonabelian transfer, the second-parabolic rank-three conclusion, and the
terminal witness.  This adapter connects the checked current producers on the
same selected `M`, `Mc`, and original rank-two data.  The rank-three branch
retains the actual alternating-six whole-core reconstruction; the G₂ branch is
supplied by the rank-three source module.  The suitable branch retains the
original 14.6.18 solvability premise and the actual mixed-size input.  Thus
singleton/quintic and terminal-solvability source work remain explicit at their
real interfaces.

Source: Aschbacher--Smith, 14.3.16, 14.6.10(5), 14.6.17--24 and 14.6.25,
printed pp.997--1001, 1028--1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/--
The fixed-`M` source endpoint after composing the current nonabelian,
rank-three, A₆/G₂, and suitable-existence adapters.  The two solvability
premises are kept separate: `hterminal` is the terminal action input for the
14.3 transfer, while `hsolv` is the original 14.6.18 statement used by the
suitable construction.
-/
theorem source_theorem_14_6_25_of_current_source_inputs
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
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
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
      hG T hempty hM hu hmany hcard e hab hsolv size

end CFSG.Quasithin.Chapter14.Section06
