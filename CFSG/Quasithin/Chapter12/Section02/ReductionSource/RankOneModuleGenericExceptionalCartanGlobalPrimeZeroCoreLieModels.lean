module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreLieModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreExceptional

/-!
# Lie-model exclusions on the original chosen zero-core pair

The same prime actor and selected right factor satisfy the literal F.1.1
hypothesis. Their different endpoint solvability excludes the split linear,
symplectic, G₂ and Ree models; the triality exclusion also uses the checked
binary moved-module argument. The fixed exceptional exclusions remain on
this same pair. No field degree is identified with the original degree n,
and no exhaustive F.1.12 recognition is asserted.
Source: Aschbacher–Smith 5.2.2, pp.647–648, applied in 12.2.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

/-- The original selected pair excludes five Lie families and every fixed
exceptional row, retaining its source Sylow, Cartans and whole overlap. -/
theorem rankOne_cartan_source_prime_pair_lie_exclusions
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
      (∀ k : ExceptionalModels.Case,
        ¬ ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R) ∧
        ¬ ExceptionalModels.ParabolicModel k (zeroCoreAmalgam L H B D R).reverse) ∧
      (∀ (F : Type) [Field F] [Finite F] [CharP F 2] (m : ℕ),
        0 < m → Nat.card F = 2^m →
        (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.LinearThree.amalgam F)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.LinearThree.amalgam F).reverse)) ∧
        (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.SymplecticFour.amalgam F)) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.SymplecticFour.amalgam F).reverse)) ∧
        (¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.G2.amalgam (F := F))) ∧
          ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
            (LieModels.G2.amalgam (F := F)).reverse))) ∧
      (∀ (m : ℕ) (hm : 0 < m),
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm))) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.Triality.amalgam (_root_.Triality.Standard.binaryParameters m hm)).reverse)) ∧
      (∀ m : ℕ,
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.ReeFour.amalgam m)) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (LieModels.ReeFour.amalgam m).reverse)) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d,hs,hz,hf,he⟩ := C.rankOne_cartan_source_prime_pair_not_exceptional
    h hmany hn hpsl hH hgen hthree c hd
  refine ⟨R,d,hs,hz,hf,he,?_,?_,?_⟩
  · intro F _ _ _ m hm hF
    exact ⟨d.zeroCore_not_linear_parabolic hi hH c hd hz hm hF,
      d.zeroCore_not_symplectic_parabolic hi hH c hd hz hm hF,
      d.zeroCore_not_g2_parabolic hi hH c hd hz hm hF⟩
  · exact fun m hm => d.zeroCore_not_triality_parabolic hi hH c hd hz m hm
  · exact fun m => d.zeroCore_not_ree_parabolic hi hH c hd hz m

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
