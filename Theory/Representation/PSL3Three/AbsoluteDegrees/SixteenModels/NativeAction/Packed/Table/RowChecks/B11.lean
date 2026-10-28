module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 11

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk99 : ∀ i : Fin 24, RowGood (99 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk100 : ∀ i : Fin 24, RowGood (100 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk101 : ∀ i : Fin 24, RowGood (101 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk102 : ∀ i : Fin 24, RowGood (102 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk103 : ∀ i : Fin 24, RowGood (103 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk104 : ∀ i : Fin 24, RowGood (104 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk105 : ∀ i : Fin 24, RowGood (105 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk106 : ∀ i : Fin 24, RowGood (106 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk107 : ∀ i : Fin 24, RowGood (107 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock11 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((11 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk99
  · exact rowChunk100
  · exact rowChunk101
  · exact rowChunk102
  · exact rowChunk103
  · exact rowChunk104
  · exact rowChunk105
  · exact rowChunk106
  · exact rowChunk107

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
