module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.FactorSelfCentralizing.Complete

/-!
# The original seed interface after factor self-centralization

The independently proved 14.3.20 excludes the strict-centralizer branch.
Consequently the original seed commutator interface is valid on that branch.
This corollary preserves the original seed and literal residual; it does not
assert that the marked point block normalizes the seed. The direct proof of
14.3.20 instead uses the factor as the existential witness allowed by 1.2.11.
There is no dependency of that proof on the corollaries below.

Source: Aschbacher--Smith, 14.3.20, pp.997--998; 1.2.11(a), p.508.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

theorem residualCommutatorSource_of_source_hypotheses
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
    (hs : Group.IsSolvable F.TerminalHdot) : ResidualCommutatorSource F (sourceResidual M Mc) := by
  intro A hA hlt P z hz hgeom hSylow
  have heq := factorSelfCentralizing_of_source_hypotheses
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs A
    hA.elementary hA.le_core hA.seed_le hA.card hA.intersection_card hA.normalized
  exact (hlt.ne heq).elim

theorem coreComponentSource_of_source_hypotheses
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
    (hs : Group.IsSolvable F.TerminalHdot) : CoreComponentSource F (sourceResidual M Mc) := by
  exact coreComponentSource_of_commutator hG T hempty hM hu hmany hcard e hnot F hne
    g hgP hgH hs (residualCommutatorSource_of_source_hypotheses
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing
