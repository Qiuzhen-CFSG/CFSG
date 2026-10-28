module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 5

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk45 : ∀ i : Fin 24, RowGood (45 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk46 : ∀ i : Fin 24, RowGood (46 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk47 : ∀ i : Fin 24, RowGood (47 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk48 : ∀ i : Fin 24, RowGood (48 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk49 : ∀ i : Fin 24, RowGood (49 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk50 : ∀ i : Fin 24, RowGood (50 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk51 : ∀ i : Fin 24, RowGood (51 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk52 : ∀ i : Fin 24, RowGood (52 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk53 : ∀ i : Fin 24, RowGood (53 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock5 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((5 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk45
  · exact rowChunk46
  · exact rowChunk47
  · exact rowChunk48
  · exact rowChunk49
  · exact rowChunk50
  · exact rowChunk51
  · exact rowChunk52
  · exact rowChunk53

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
