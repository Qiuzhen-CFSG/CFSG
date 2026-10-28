module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 2

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk18 : ∀ i : Fin 24, RowGood (18 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk19 : ∀ i : Fin 24, RowGood (19 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk20 : ∀ i : Fin 24, RowGood (20 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk21 : ∀ i : Fin 24, RowGood (21 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk22 : ∀ i : Fin 24, RowGood (22 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk23 : ∀ i : Fin 24, RowGood (23 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk24 : ∀ i : Fin 24, RowGood (24 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk25 : ∀ i : Fin 24, RowGood (25 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk26 : ∀ i : Fin 24, RowGood (26 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock2 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((2 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk18
  · exact rowChunk19
  · exact rowChunk20
  · exact rowChunk21
  · exact rowChunk22
  · exact rowChunk23
  · exact rowChunk24
  · exact rowChunk25
  · exact rowChunk26

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
