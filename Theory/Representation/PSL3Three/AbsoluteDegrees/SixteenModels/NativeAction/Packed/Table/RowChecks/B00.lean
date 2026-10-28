module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 0

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk0 : ∀ i : Fin 24, RowGood (0 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk1 : ∀ i : Fin 24, RowGood (1 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk2 : ∀ i : Fin 24, RowGood (2 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk3 : ∀ i : Fin 24, RowGood (3 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk4 : ∀ i : Fin 24, RowGood (4 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk5 : ∀ i : Fin 24, RowGood (5 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk6 : ∀ i : Fin 24, RowGood (6 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk7 : ∀ i : Fin 24, RowGood (7 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk8 : ∀ i : Fin 24, RowGood (8 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock0 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((0 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk0
  · exact rowChunk1
  · exact rowChunk2
  · exact rowChunk3
  · exact rowChunk4
  · exact rowChunk5
  · exact rowChunk6
  · exact rowChunk7
  · exact rowChunk8

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
