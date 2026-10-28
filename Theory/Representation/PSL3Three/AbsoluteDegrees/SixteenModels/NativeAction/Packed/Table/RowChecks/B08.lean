module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 8

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk72 : ∀ i : Fin 24, RowGood (72 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk73 : ∀ i : Fin 24, RowGood (73 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk74 : ∀ i : Fin 24, RowGood (74 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk75 : ∀ i : Fin 24, RowGood (75 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk76 : ∀ i : Fin 24, RowGood (76 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk77 : ∀ i : Fin 24, RowGood (77 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk78 : ∀ i : Fin 24, RowGood (78 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk79 : ∀ i : Fin 24, RowGood (79 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk80 : ∀ i : Fin 24, RowGood (80 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock8 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((8 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk72
  · exact rowChunk73
  · exact rowChunk74
  · exact rowChunk75
  · exact rowChunk76
  · exact rowChunk77
  · exact rowChunk78
  · exact rowChunk79
  · exact rowChunk80

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
