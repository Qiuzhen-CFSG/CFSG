module
public import CFSG.Quasithin.Chapter15.Section01.SourceRankTwoResolver
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SolvableAssembly

/-!
# Rank-two resolver after the original nonabelian assembly

The resolver consumes the completed nonabelian transfer endpoint.  Its only
nonabelian source family is terminal solvability for each selected ordering
maximal subgroup; the rank-three and terminal-witness inputs remain the two
independent abelian premises of 14.6.25.

Source: Aschbacher--Smith, 14.6.25 and 15.1.3, printed pp.1042 and 1086--1089.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 ChapterA.Section05To06 Chapter12.Section08 Chapter14.SourcePreliminaries
open Chapter14.Section06
open Chapter14.Section03.NonabelianSource.SourceAbelianReduction
variable {G : Type*} [Group G] [Finite G]

/-- The literal rank-two resolver with the proved self-centralization,
outside-nonfusion and core-collapse producers composed into its nonabelian
branch. -/
theorem source_rankTwoResolver_of_solvable_source_inputs
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {Mc : Subgroup G}
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hsolvable : ∀ (M : Subgroup G), IsOrderingMaximal T M → M ≠ Mc →
      RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M →
      (¬ ClassificationModels.IsTheoremEModel G →
        ∀ (F : InvariantFlag T (rankTwoSeed T M) 2), ¬ IsMulCommutative F.U →
        ∀ g ∈ F.P (sourceResidual M Mc), g ∉ F.H → Group.IsSolvable F.TerminalHdot))
    (hthree : ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceSecondParabolicRankThree hG T hempty hM hunique hmany hcard e hab)
    (hwitness : ¬ ClassificationModels.IsTheoremEModel G →
      ∀ (M : Subgroup G) (hM : IsOrderingMaximal T M), M ≠ Mc →
      ∀ (hcard : Nat.card (localModule T M) = 4)
      (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
      (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)),
      SourceTerminalWitness hG T hempty hM hunique hmany hcard e hab) :
    RankTwoResolver T Mc := by
  apply source_rankTwoResolver_of_source_inputs hG T hempty hunique hmany ?_ hthree hwitness
  intro M hM hneM hrank
  exact source_theoremE_of_nonabelian_of_solvable hG T hempty hM hunique hmany hrank
    (hsolvable M hM hneM hrank)

end CFSG.Quasithin.Chapter15.Section01
