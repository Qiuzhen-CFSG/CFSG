module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeUnitarySelection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanRankOneSelection

/-!
# The complete single-Bender selection in the chosen-module argument

The original E.2.2 single-component marking now supplies the actual residual
prime pair in all three Bender families. In the unitary case the intrinsic
quotient is recognized as SU₃ or PSU₃ over the same field; it is not replaced
by the source projective image without proof. The literal pair satisfies
genuine F.1.1 and has trivial generated two-core. Exclusion of those zero-core
models and the final normalization remain with the Cartan local-to-global task.
Source: Aschbacher–Smith 5.1.10(2),5.2.2, pp.634,646–648, and 12.2.2, p.795.
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

/-- Every original single-Bender source row constructs the actual residual prime pair. -/
theorem rankOne_cartan_single_bender_prime_pair
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
    (hm : BenderModel ((normalizer (L : Set G)).subgroupOf H) C f) :
    LocalData T L H B D (residual H) ∧
      (generated L H D (residual H)).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,residual H]
        (Global.sourceS L H) :=
  single_bender_prime_pair (M.rankOne_generic_input_of_many h hmany hn hpsl)
    hH c hd hC hqs hc hm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
