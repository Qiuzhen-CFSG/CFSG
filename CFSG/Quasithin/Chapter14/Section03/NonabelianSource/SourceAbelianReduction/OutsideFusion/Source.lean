module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.CosetOrbit
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.ResidualAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.MovedSeed
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.MovedCentralizerOrder
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction

/-!+# Original 14.3.21(2): nonfusion outside RQ

For an outside involution fixing the seed, transitivity on its R-coset gives
the centralizer's residual generation and hence the marked point's return
to the conjugate of Q. For an involution moving the seed, the order-eight
centralizer gives the same return. The square-root obstruction then excludes
fusion with the marked point, retaining the original Q = O₂(H).

The source theorem assumes only the original setup and terminal solvability.
Its application below discharges the nonfusion input of the nonabelian
Theorem E reduction; solvability, factor self-centralization and core collapse
remain with their source owners.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Original 14.3.21(2), with terminal solvability explicit and both
core-return cases discharged on the original R and Q. -/
theorem source_outside_point_nonfusion_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot) :
    OutsidePointNonfusion F (sourceResidual M Mc) := by
  have horbit := source_fixed_seed_coset_transitivity_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hres := source_fixed_seed_residual_generation_of_coset_transitivity
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs horbit
  have hfixed := source_fixed_seed_core_return_of_residual_generation
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hres
  have hmoved := source_moved_seed_core_return_of_centralizer_card
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (fun t ht ht2 htout htV => source_moved_centralizer_card_eight
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t ht ht2 htout htV)
  exact source_outside_point_nonfusion_of_core_returns
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hfixed hmoved

/-- The literal nonabelian Theorem E consumer with its `hnonfusion` premise
discharged by original 14.3.21(2). The other three source inputs are preserved. -/
theorem source_theoremE_of_nonabelian_of_solvable_self_and_collapse
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
    (hcollapse : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot →
        FactorSelfCentralizing F (sourceResidual M Mc) →
        OutsidePointNonfusion F (sourceResidual M Mc) → F.H.pCoreIn 2 = F.U)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
    hsolvable hself ?_ hcollapse hne
  intro hnot F hneF g hgP hgH hs
  obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  let := rankTwoSeed_elementary (source_lemma_14_2_4 hG T hempty hM hu hmany hcard e)
  exact source_outside_point_nonfusion_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hneF g hgP hgH hs

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
