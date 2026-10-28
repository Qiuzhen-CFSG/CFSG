module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.SeedCommutator
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Reduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Even.Models
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.ModelExclusion.Sporadic.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction

/-!
# The nonabelian consumer of the marked 14.3.20 reduction

The source self-centralization theorem now discharges the corresponding
premise in the actual nonabelian Theorem E transfer. The earlier conditional
marked-input API is preserved. Solvability, outside-point nonfusion and core
collapse remain explicit inputs owned by the nonabelian assembly task
`qt-e-14316-nonabelian`; this module does not claim the whole Theorem E result.

Source: Aschbacher--Smith, 14.3.20--22 and 14.6.25.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem source_theoremE_of_nonabelian_of_marked_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hsolvable : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot)
    (hinputs : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FourCenterSource F (sourceResidual M Mc) ∧
        CoreComponentSource F (sourceResidual M Mc) ∧
        ModelExclusionSource F (sourceResidual M Mc))
    (hnonfusion : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        OutsidePointNonfusion F (sourceResidual M Mc))
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
    hsolvable ?_ hnonfusion hcollapse hne
  intro hnot F hneF g hgP hgH hs
  obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  let := rankTwoSeed_elementary (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
  obtain ⟨hgeometry, hcore, hexclude⟩ := hinputs hnot F hneF g hgP hgH hs
  exact factorSelfCentralizing_of_source_inputs hG T hempty hM hu hmany hcard e hnot
    F hneF g hgP hgH hs hgeometry hcore hexclude

/-- The nonabelian transfer with original 14.3.20 discharged. -/
theorem source_theoremE_of_nonabelian_of_selfCentralizing_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hsolvable : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot)
    (hnonfusion : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        OutsidePointNonfusion F (sourceResidual M Mc))
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
    hsolvable ?_ hnonfusion hcollapse hne
  intro hnot F hneF g hgP hgH hs
  obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  let := rankTwoSeed_elementary (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
  exact factorSelfCentralizing_of_source_hypotheses hG T hempty hM hu hmany hcard e hnot
    F hneF g hgP hgH hs

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
