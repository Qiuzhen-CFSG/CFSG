module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreExceptional
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit

/-!
# Exceptional zero-core exclusions on the original chosen pair

The source construction and changed-Sylow exclusion supply the same
zero-core prime pair. Its nonsolvable right factor and original moved
module exclude every fixed exceptional F.1.12 row in either orientation.
The literal source Sylow and whole overlap are preserved. Exhaustive
recognition and the higher-degree small-Cartan argument remain required.
Source: Aschbacher–Smith 5.2.2, pp.647–648, applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The selected zero-core pair has no fixed exceptional parabolic model,
with the weaker Hall–Janko equivalence convention included. -/
theorem rankOne_cartan_source_prime_pair_not_exceptional
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n p : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (generated L H D R).pCoreIn 2 = ⊥ ∧
      ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) ∧
      ∀ k : ChapterF.GreenBook.ExceptionalModels.Case,
        ¬ ChapterF.GreenBook.ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R) ∧
        ¬ ChapterF.GreenBook.ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R).reverse := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d,hs,hz,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨R,d,hs,hz,hf,fun k => d.zeroCore_not_exceptional_parabolic hi hH c hd hz k⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
