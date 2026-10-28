module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 10

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk90 : ∀ i : Fin 24, RowGood (90 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk91 : ∀ i : Fin 24, RowGood (91 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk92 : ∀ i : Fin 24, RowGood (92 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk93 : ∀ i : Fin 24, RowGood (93 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk94 : ∀ i : Fin 24, RowGood (94 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk95 : ∀ i : Fin 24, RowGood (95 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk96 : ∀ i : Fin 24, RowGood (96 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk97 : ∀ i : Fin 24, RowGood (97 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk98 : ∀ i : Fin 24, RowGood (98 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock10 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((10 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk90
  · exact rowChunk91
  · exact rowChunk92
  · exact rowChunk93
  · exact rowChunk94
  · exact rowChunk95
  · exact rowChunk96
  · exact rowChunk97
  · exact rowChunk98

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
