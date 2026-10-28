module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 12

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk108 : ∀ i : Fin 24, RowGood (108 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk109 : ∀ i : Fin 24, RowGood (109 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk110 : ∀ i : Fin 24, RowGood (110 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk111 : ∀ i : Fin 24, RowGood (111 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk112 : ∀ i : Fin 24, RowGood (112 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk113 : ∀ i : Fin 24, RowGood (113 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk114 : ∀ i : Fin 24, RowGood (114 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk115 : ∀ i : Fin 24, RowGood (115 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk116 : ∀ i : Fin 24, RowGood (116 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock12 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((12 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk108
  · exact rowChunk109
  · exact rowChunk110
  · exact rowChunk111
  · exact rowChunk112
  · exact rowChunk113
  · exact rowChunk114
  · exact rowChunk115
  · exact rowChunk116

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
