module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitaryModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels

/-!
# Unitary filters on the original chosen prime pair

The original construction supplies the same selected right factor, source
Sylow and whole overlap as the preceding exceptional and Lie-model filters.
Both orientations of every unitary-four model and its actual degree-two
extension, and of the unitary-five model at parameter four, are excluded.
The extension argument transports the normal Sylow of the whole source
overlap; it does not use the false printed full-overlap two-core identity.

This completes the concrete catalogue filters on this pair. Exhaustive
source-restricted recognition, original higher-field reduction and final
Cartan normalization remain separate mathematical obligations.
Source: Aschbacher–Smith 5.2.2, pp.647–648, and F.1.12(I)(6–7),
pp.263–264, applied in 12.2.2, p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

/-- All remaining unitary catalogue rows are excluded on the original prime
pair, without changing its source Sylow, selected factor or field degrees. -/
theorem rankOne_cartan_source_prime_pair_unitary_exclusions
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
      (∀ (m : ℕ) (hm : 1 ≤ m),
        (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.UnitaryFour.amalgam m hm)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.UnitaryFour.amalgam m hm).reverse)) ∧
        (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.UnitaryFour.Extension.amalgam m hm)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.UnitaryFour.Extension.amalgam m hm).reverse))) ∧
      (∀ M : UnitaryFive.Model 4,
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          M.amalgam) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          M.amalgam.reverse)) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d,hs,hz,hf,_⟩ := C.rankOne_cartan_source_prime_pair_lie_exclusions
    h hmany hn hpsl hH hgen hthree c hd
  refine ⟨R,d,hs,hz,hf,?_,?_⟩
  · intro m hm
    exact ⟨d.zeroCore_not_unitaryFour_parabolic hi hH c hd hz m hm,
      d.zeroCore_not_unitaryFourExtension_parabolic hi hH c hd hz m hm⟩
  · exact fun M => d.zeroCore_not_unitaryFive_parabolic hi hH c hd hz M

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
