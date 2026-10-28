module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.Sieve
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction

/-!
# The terminal solvability assembly and its nonabelian consumer

The existing empty-family sieve eliminates four actual quotient rows.
The remaining source work is the component catalogue, the small dotted
A₅/A₆ actions (including the exchanged A₅ orbit), and the L₂(8) Borel
contradiction. Once these three inputs are proved, the first theorem yields
the literal solvability input of the original nonabelian transfer argument.
The second theorem applies it to that argument on the same M, Mc and flag.

This module does not claim unconditional solvability or 14.3.15: all three
missing inputs remain explicit, as do the independent later transfer inputs.
Source: Aschbacher--Smith 14.3.13--16, printed pp.993--995.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Conditional solvability of the original terminal action, with precisely
the catalogue and two unproved source branches still explicit. -/
theorem source_terminal_solvable_of_component_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2) (g : G)
    (hcases : ¬ Group.IsSolvable F.TerminalHdot →
      ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K)
    (hsmall : ∀ K : Subgroup G, ComponentLift F g K → SmallImageRow F K → False)
    (height : ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False) :
    Group.IsSolvable F.TerminalHdot := by
  classical
  by_contra hn
  obtain ⟨K, hK, hc⟩ := hcases hn
  rcases source_component_cases_reduce hG T hempty hM hu hmany hcard e hnot F g K hK hc
    with hs | h8
  · exact hsmall K hK hs
  · exact height K hK h8

/-- The exact nonabelian transfer consumer with terminal solvability reduced
to the three component-source obligations. The other transfer inputs are unchanged. -/
theorem source_theoremE_of_nonabelian_of_component_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hrank : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M)
    (hcatalogue : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → ¬ Group.IsSolvable F.TerminalHdot →
        ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K)
    (hsmall : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
      ∀ K : Subgroup G, ComponentLift F g K → SmallImageRow F K → False)
    (height : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
      ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H →
      ∀ K : Subgroup G, ComponentLift F g K → EightImageRow F K → False)
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
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) Mc)) :
    ClassificationModels.IsTheoremEModel G := by
  apply source_theoremE_of_nonabelian_of_inputs hG T hempty hM hu hmany hrank
    ?_ hself hnonfusion hcollapse hne
  intro hnot F hneF g hgP hgH
  obtain ⟨hcard, ⟨e⟩⟩ := Section06.source_plane_of_rankTwo hrank
  exact source_terminal_solvable_of_component_inputs hG T hempty hM hu hmany hcard e hnot F g
    (hcatalogue hnot F hneF g hgP hgH)
    (hsmall hnot F hneF g hgP hgH)
    (height hnot F hneF g hgP hgH)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
