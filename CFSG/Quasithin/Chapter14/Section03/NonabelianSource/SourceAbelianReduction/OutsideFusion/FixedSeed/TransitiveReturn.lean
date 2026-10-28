module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.ResidualAction
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed

/-!
# Fixed-seed core return from the independent coset orbit assertion

The centralizer action now discharges the residual-generation premise of
the original conjugation-to-core argument. Only the coset transitivity
premise remains for the source assembly owner.

Source: Aschbacher--Smith, Quasithin Groups, 14.3.21(2), printed p.998.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The preceding residual step now feeds the original fixed-seed core-return
consumer, with only the independent coset transitivity premise remaining. -/
theorem source_fixed_seed_core_return_of_coset_transitivity
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
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (horbit : FixedSeedCosetTransitivity F (sourceResidual M Mc)) :
    FixedSeedCoreReturn F (sourceResidual M Mc) := by
  exact source_fixed_seed_core_return_of_residual_generation
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (source_fixed_seed_residual_generation_of_coset_transitivity
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs horbit)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
