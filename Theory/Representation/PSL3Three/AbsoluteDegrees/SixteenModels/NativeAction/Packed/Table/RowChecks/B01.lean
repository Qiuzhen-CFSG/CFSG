module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 1

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk9 : ∀ i : Fin 24, RowGood (9 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk10 : ∀ i : Fin 24, RowGood (10 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk11 : ∀ i : Fin 24, RowGood (11 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk12 : ∀ i : Fin 24, RowGood (12 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk13 : ∀ i : Fin 24, RowGood (13 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk14 : ∀ i : Fin 24, RowGood (14 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk15 : ∀ i : Fin 24, RowGood (15 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk16 : ∀ i : Fin 24, RowGood (16 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk17 : ∀ i : Fin 24, RowGood (17 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock1 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((1 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk9
  · exact rowChunk10
  · exact rowChunk11
  · exact rowChunk12
  · exact rowChunk13
  · exact rowChunk14
  · exact rowChunk15
  · exact rowChunk16
  · exact rowChunk17

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
