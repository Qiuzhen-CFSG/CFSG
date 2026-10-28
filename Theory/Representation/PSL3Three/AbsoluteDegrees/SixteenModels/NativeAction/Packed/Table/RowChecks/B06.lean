module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 6

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk54 : ∀ i : Fin 24, RowGood (54 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk55 : ∀ i : Fin 24, RowGood (55 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk56 : ∀ i : Fin 24, RowGood (56 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk57 : ∀ i : Fin 24, RowGood (57 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk58 : ∀ i : Fin 24, RowGood (58 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk59 : ∀ i : Fin 24, RowGood (59 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk60 : ∀ i : Fin 24, RowGood (60 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk61 : ∀ i : Fin 24, RowGood (61 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk62 : ∀ i : Fin 24, RowGood (62 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock6 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((6 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk54
  · exact rowChunk55
  · exact rowChunk56
  · exact rowChunk57
  · exact rowChunk58
  · exact rowChunk59
  · exact rowChunk60
  · exact rowChunk61
  · exact rowChunk62

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
