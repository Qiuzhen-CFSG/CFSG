module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 7

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk63 : ∀ i : Fin 24, RowGood (63 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk64 : ∀ i : Fin 24, RowGood (64 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk65 : ∀ i : Fin 24, RowGood (65 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk66 : ∀ i : Fin 24, RowGood (66 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk67 : ∀ i : Fin 24, RowGood (67 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk68 : ∀ i : Fin 24, RowGood (68 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk69 : ∀ i : Fin 24, RowGood (69 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk70 : ∀ i : Fin 24, RowGood (70 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk71 : ∀ i : Fin 24, RowGood (71 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock7 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((7 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk63
  · exact rowChunk64
  · exact rowChunk65
  · exact rowChunk66
  · exact rowChunk67
  · exact rowChunk68
  · exact rowChunk69
  · exact rowChunk70
  · exact rowChunk71

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
