module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreUnitary
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanZeroCoreTrialityExclusion

/-!
# All four marked zero-core exclusions for the original Chapter 12 pair

The constructed source pair has |S| > 2^(3n). This excludes both
orientations of the genuine U₄(2) model, whose Sylow two-subgroups have
order 64. Combining the checked Hall–Janko and binary-triality exclusions
removes all four marked rows in the source argument, including either
orientation of the Lie-type models.

The actual recognition theorem still has to give one of these markings;
faithful local geometry alone has not supplied that theorem. Its proof,
the higher-field reduction and changed-Sylow assembly remain with
qt-d-1222-rankone-cartan-local-to-global, which retains the final
conditional normalization theorem with the original h513 input.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.647–648,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- The literal selected source pair excludes all four marked zero-core models.
No model-recognition premise or identification of S with T is asserted. -/
theorem rankOne_cartan_source_zeroCore_model_exclusions
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      2^(3*n) < Nat.card (Global.sourceS L H) ∧
      ((generated L H D R).pCoreIn 2 = ⊥ →
        ¬ ChapterF.GreenBook.HallJanko.IsJ2ParabolicModel (zeroCoreAmalgam L H B D R) ∧
        ¬ ChapterF.GreenBook.HallJanko.IsAutJ2ParabolicModel (zeroCoreAmalgam L H B D R) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          binaryTrialityPrimeAmalgam) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          binaryTrialityPrimeAmalgam.reverse) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (amalgam 1 (by decide))) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          (amalgam 1 (by decide)).reverse)) := by
  let hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d⟩ := source_prime_pair hi hH hpar hthree c hd
  refine ⟨R,d,d.sourceS_card_gt hi hH c hd,fun hz => ?_⟩
  refine ⟨d.zeroCore_not_janko_parabolic hi hH c hd hz,
    d.zeroCore_not_autJanko_parabolic hi hH c hd hz,
    d.zeroCore_not_binaryTriality_parabolic hi hH c hd hz,?_,
    d.zeroCore_not_binaryUnitary_parabolic hi hH c hd⟩
  rintro ⟨e⟩
  exact d.zeroCore_not_binaryTriality_central_right hz ⟨e.right⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
