module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeRankOneSelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The selected residual pair in the chosen-module Cartan argument

The actual rank-one residual supplies the whole right-factor geometry and
forces the zero-core branch of the prime-actor argument. The second
application starts with the original single linear/Suzuki E.2.2 marking;
it proves the intrinsic quotient identification instead of assuming it.
Both results use the original source S, residual, prime actor and Hall pair
in genuine F.1.1. The remaining model exclusions and normalization assembly
stay with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, pp.646–648, applied to 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- Construct the local pair and its genuine zero-core amalgam on the literal residual. -/
theorem rankOne_cartan_residual_prime_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hm : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)))
    (hqs : IsQuasisimple ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H))) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) :=
  rankOne_residual_prime_pair (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hm hqs

/-- E.2.2's original single linear/Suzuki marking discharges the right-factor selection. -/
theorem rankOne_cartan_single_linear_suzuki_prime_pair
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p f : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) :=
  single_linear_suzuki_prime_pair (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hC hqs hc hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
