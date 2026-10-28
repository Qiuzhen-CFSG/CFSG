module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Six.SourceCubic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubic

/-!
# Excluding the original degree-six terminal branch

The proved cubic Fitting theorem supplies a normal cubic subgroup in every
faithful irreducible degree-six source action. The original cubic-index
argument excludes that subgroup when the center is the marked point. All
three-core ranks and structures are discharged while preserving the actual
terminal quotient and representation.

Source: Aschbacher--Smith 14.3.15 and G.9.4, printed pp.994,355.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original degree-six cubic branch is impossible. -/
theorem false_of_degree_six
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    {A : Subgroup F.TerminalHdot}
    (h : ChapterG.Section09.FittingHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,A⁆ : Subgroup F.TerminalHdot))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 6) : False := by
  obtain ⟨C,hCn,hCc⟩ :=
    ChapterG.Section09.FittingRecognition.Six.normal_cubic_of_source_degree_six h hc hd
  let := hCn
  exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hCc

/-- The original degree-six cubic branch is impossible once its high-rank
three-core alternative has been excluded. -/
theorem false_of_degree_six_three_rank_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (d : ClosureGeometry F) (hZ : F.ZU = F.Vi 1)
    {A : Subgroup F.TerminalHdot}
    (h : ChapterG.Section09.FittingHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup F.TerminalHdot,A⁆ : Subgroup F.TerminalHdot))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 6)
    (hr : primeRank 3 (pCore 3 F.TerminalHdot) ≤ 2) : False := by
  obtain ⟨C,hCn,hCc⟩ :=
    ChapterG.Section09.FittingRecognition.Six.normal_cubic_of_source_three_rank_le_two h hc hd hr
  let := hCn
  exact no_normal_cubic_of_center_point hG T hempty hM hu hmany hcard e hnot F d hZ C hCc


end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
