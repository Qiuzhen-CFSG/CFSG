module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.Completion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.Source
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementCyclicSpan
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.Local
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.ResidualFusion
public import CFSG.Quasithin.Chapter14.Section06.SourceTheorem14625

/-!
# The literal 14.6.25 consumer of the nonabelian transfer reduction

The four nonabelian source inputs feed the proved final transfer argument.
This supplies the nonabelian premise of the existing 14.6.25 assembly on
its original M, Mc and residual. The independent abelian rank-three and
terminal-witness premises stay with the 14.6.25 owner.

This is a conditional assembly: none of its source inputs is asserted here.
Source: Aschbacher--Smith, proof of 14.6.25, printed p.1042.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

/-- Apply the completed transfer implication to the actual 14.6.25 consumer.
All missing source families remain explicit. -/
theorem source_theorem_14_6_25_of_nonabelian_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hsolvable : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot)
    (hself : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc))
    (hnonfusion : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        OutsidePointNonfusion F (sourceResidual M Mc))
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hthree : ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceSecondParabolicRankThree hG T hempty hM hu hmany hcard e hab)
    (hwitness : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceTerminalWitness hG T hempty hM hu hmany hcard e hab) :
    ClassificationModels.IsTheoremEModel G := by
  exact source_theorem_14_6_25_of_source_inputs hG T hempty hM hu hmany hrank
    (source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
      hsolvable hself hnonfusion hcollapse) hthree hwitness

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
