module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 3

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk27 : ∀ i : Fin 24, RowGood (27 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk28 : ∀ i : Fin 24, RowGood (28 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk29 : ∀ i : Fin 24, RowGood (29 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk30 : ∀ i : Fin 24, RowGood (30 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk31 : ∀ i : Fin 24, RowGood (31 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk32 : ∀ i : Fin 24, RowGood (32 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk33 : ∀ i : Fin 24, RowGood (33 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk34 : ∀ i : Fin 24, RowGood (34 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk35 : ∀ i : Fin 24, RowGood (35 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock3 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((3 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk27
  · exact rowChunk28
  · exact rowChunk29
  · exact rowChunk30
  · exact rowChunk31
  · exact rowChunk32
  · exact rowChunk33
  · exact rowChunk34
  · exact rowChunk35

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
