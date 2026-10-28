module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeQuinticSolvableLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.BinaryRows

/-!
# Binary reduced-row filters for the literal Chapter 6 quintic pair

The Chapter 6 zero-core construction supplies the same pair
`![D ⊔ sourceS, R]` used by the F.1.12 quintic branch.  This module applies
the source-level binary local, join, and full-parabolic filters to that pair,
retaining the actual D₁₀/Sz(2) left quotient and the original full Borel.
The regular and exceptional reduced rows are intentionally left to the
exhaustive DGS source selection.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

theorem LocalData.quintic_binary_row_filters
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H 5 D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
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
  let S := Global.sourceS L H
  let J := D ⊔ S
  have hf := d.hypothesisF11 h hH c hd hz
  have hi := Input.prime_left_index h hH c hd
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro he
    exact hf.quintic_no_binary_local_left le_sup_right hi he
  · intro he
    exact hf.quintic_solvable_of_binary_local_right he
  · intro he
    exact hf.quintic_no_binary_join_left le_sup_right hi he
  · intro he
    exact hf.quintic_solvable_of_binary_join_right le_sup_right hi he
  · intro he
    exact hf.quintic_solvable_of_binary_parabolic_right he

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
