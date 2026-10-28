module
public import CFSG.Quasithin.Chapter14.Section06.SourceSingletonCompatibility.Assembly
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625EarlierFactors

/-!
# Original 14.6.25 with the singleton source inputs separated

The fixed-M classification now uses the proved construction of the full
exchanged-factor family, including its application to every fresh cubic
Borel subgroup. The unresolved elementary-nine exclusion, quintic outer
exclusion and cyclic first-parabolic alternatives remain explicit. The
existing nonabelian terminal-solvability, A6 reconstruction and mixed-size
inputs are unchanged; no premise is silently discharged by this assembly.

Source: Aschbacher--Smith 14.6.12 and 14.6.25, printed pp.1031 and 1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original rank-two classification, conditional on the literal
remaining source branches. Final discharge stays with the source owners. -/
theorem source_theorem_14_6_25_of_singleton_inputs
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
    (hfirst : SourceSingletonCompatibility.QuinticFirstParabolics T M)
    (hnine : ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceSingletonCompatibility.NineExclusion T M)
    (houter : ¬ ClassificationModels.IsTheoremEModel G →
      IsMulCommutative (conjugateSpanBy (localModule T M) Mc) →
        SourceSingletonCompatibility.QuinticOuterExclusion T M)
    (size : Chapter10.MixedZeroCore.MixedSizeInput G) :
    ClassificationModels.IsTheoremEModel G := by
  obtain ⟨hcard,⟨e⟩⟩ := source_plane_of_rankTwo hrank
  exact source_theorem_14_6_25_of_earlier_factors hG T hempty hM hu hmany hrank ha hterminal
    (fun hnot hab => source_exchanged_factor_family_of_singleton_inputs
      hG T hempty hM hu hmany hcard e hab hnot hfirst (hnine hnot hab) (houter hnot hab)) size

end CFSG.Quasithin.Chapter14.Section06
