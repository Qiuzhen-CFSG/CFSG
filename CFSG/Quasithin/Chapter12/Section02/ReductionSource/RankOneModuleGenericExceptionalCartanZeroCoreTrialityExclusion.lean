module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTrialityExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanZeroCoreModels

/-!
# Excluding the marked binary-triality row in the original Chapter 12 pair

The source factor construction supplies its actual local pair. In the
zero-core branch the original omega-generated module has order at least
sixteen and is fixed by the original seven-subgroup. The genuine triality
Borel bounds this same subgroup by eight, excluding its parabolic marking.
Together with the checked Hall–Janko bounds this removes all three of those
marked models, without assuming equality of the overlap and full Sylow.

Recognition of the original pair, the unitary row, higher-field reduction
and the changed-Sylow assembly remain with the source normalization owner
qt-d-1222-rankone-cartan-local-to-global. These exclusions do not assert
that an arbitrary faithful triple has one of the listed model markings.
Source: Aschbacher–Smith 5.2.2 and 12.2.2, printed pp.647–648,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B D : Subgroup G} (M : ChosenModule T L V)
include M

/-- Construct the literal prime pair and exclude the genuine J₂, Aut(J₂)
and binary-triality markings whenever its two-core is trivial. -/
theorem rankOne_cartan_source_zeroCore_not_janko_triality
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n p : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧
      ((generated L H D R).pCoreIn 2 = ⊥ →
        ¬ ChapterF.GreenBook.HallJanko.IsJ2ParabolicModel (zeroCoreAmalgam L H B D R) ∧
        ¬ ChapterF.GreenBook.HallJanko.IsAutJ2ParabolicModel (zeroCoreAmalgam L H B D R) ∧
        ¬ Nonempty (RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
          binaryTrialityPrimeAmalgam)) := by
  let hi := M.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d⟩ := source_prime_pair hi hH hpar hthree c hd
  exact ⟨R,d,fun hz => ⟨d.zeroCore_not_janko_parabolic hi hH c hd hz,
    d.zeroCore_not_autJanko_parabolic hi hH c hd hz,
    d.zeroCore_not_binaryTriality_parabolic hi hH c hd hz⟩⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
