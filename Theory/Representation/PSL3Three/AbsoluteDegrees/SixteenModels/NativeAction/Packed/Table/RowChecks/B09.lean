module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 9

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk81 : ∀ i : Fin 24, RowGood (81 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk82 : ∀ i : Fin 24, RowGood (82 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk83 : ∀ i : Fin 24, RowGood (83 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk84 : ∀ i : Fin 24, RowGood (84 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk85 : ∀ i : Fin 24, RowGood (85 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk86 : ∀ i : Fin 24, RowGood (86 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk87 : ∀ i : Fin 24, RowGood (87 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk88 : ∀ i : Fin 24, RowGood (88 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk89 : ∀ i : Fin 24, RowGood (89 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock9 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((9 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk81
  · exact rowChunk82
  · exact rowChunk83
  · exact rowChunk84
  · exact rowChunk85
  · exact rowChunk86
  · exact rowChunk87
  · exact rowChunk88
  · exact rowChunk89

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
