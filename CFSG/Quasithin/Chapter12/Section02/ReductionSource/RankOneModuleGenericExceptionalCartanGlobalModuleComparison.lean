module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalModuleComparison
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original escaping prime pair with the module cases discharged

The comparison of the original reduced module and its omega-span closes
the mixed Thompson-action case. The complete small-generation theorem
now supplies a prime actor for every escaping Cartan under universal
local control. The existing source construction selects the right factor
and proves zero core and F.1.1 on the same original sourceS.

This application retains the original residual, both Hall Cartans, hthree
and the component/parabolic distinction. It takes no additional movement,
module model, constituent invariance or field-degree premise. The later
zero-core recognition and global normalization remain to be proved.

Source: Aschbacher--Smith 5.1.2--6 and 5.2.2, pp.630--633,647--649,
with the 12.2.2 application on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Every original escaping Cartan has small generation and the literal
selected zero-core prime pair, with all module-action cases discharged. -/
theorem rankOne_cartan_smallGeneration_and_prime_pair_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G)) :
    CartanSmallGeneration A H n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  have hs := sourceCartanSmallGeneration T L (RankOneModule.wholeReduced T L) n hi
    H hH hgen A B c hcontrol hz
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hselected,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hs,p,D,R,hd,d,hselected,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
