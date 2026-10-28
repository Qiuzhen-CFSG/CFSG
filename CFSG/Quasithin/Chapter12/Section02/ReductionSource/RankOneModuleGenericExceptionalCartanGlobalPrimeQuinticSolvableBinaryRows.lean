module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableBinaryRows
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableLocal

/-!
# Binary quintic-row filters in the Chapter 12 application

The chosen-module source construction produces the literal zero-core pair used
by Chapter F.  The Chapter 6 binary filters therefore apply without changing
the selected factor, the full Borel, or the inherited quasithin hypothesis.
This is a conditional branch result: regular and exceptional reduced rows
still require the exhaustive DGS source assembly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

theorem rankOne_cartan_quintic_binary_filters
    {T : Sylow 2 G} {L V H A B D : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (generated L H D R).pCoreIn 2 = ⊥ ∧
      let S := Global.sourceS L H
      let J := D ⊔ S
      (∀ _ : ClassicalGroup.IsPSL ((![J,R] (0 : Fin 2)) ⧸
        pCore 2 (![J,R] (0 : Fin 2))) 2 2, False) ∧
      (∀ _ : ClassicalGroup.IsPSL ((![J,R] (1 : Fin 2)) ⧸
        pCore 2 (![J,R] (1 : Fin 2))) 2 2,
        Group.IsSolvable (ChapterF.Source.parabolic ![J,R] S 1)) ∧
      (∀ _ : ClassicalGroup.IsPSL
        ((![J,R] (0 : Fin 2) ⊔ ChapterF.Source.SuzukiContainment.reducedSylow
          ![J,R] S : Subgroup G) ⧸ pCore 2 (![J,R] (0 : Fin 2) ⊔
            ChapterF.Source.SuzukiContainment.reducedSylow ![J,R] S : Subgroup G)) 2 2,
        False) ∧
      (∀ _ : ClassicalGroup.IsPSL
        ((![J,R] (1 : Fin 2) ⊔ ChapterF.Source.SuzukiContainment.reducedSylow
          ![J,R] S : Subgroup G) ⧸ pCore 2 (![J,R] (1 : Fin 2) ⊔
            ChapterF.Source.SuzukiContainment.reducedSylow ![J,R] S : Subgroup G)) 2 2,
        Group.IsSolvable (ChapterF.Source.parabolic ![J,R] S 1)) ∧
      (∀ _ : ClassicalGroup.IsPSL
        (ChapterF.Source.parabolic ![J,R] S 1 ⧸
          pCore 2 (ChapterF.Source.parabolic ![J,R] S 1)) 2 2,
        Group.IsSolvable (ChapterF.Source.parabolic ![J,R] S 1)) := by
  let hi := C.rankOne_generic_input_of_many h hmany hn hpsl
  obtain ⟨R,d,hs,hz,_⟩ := C.rankOne_cartan_source_prime_pair_zero_core
    h hmany hn hpsl hH hgen hthree c hd
  refine ⟨R,d,hs,hz,?_⟩
  exact d.quintic_binary_row_filters hi hH c hd hz

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
