module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.Defs

/-!
# Row certificate batch 4

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `RowChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem rowChunk36 : ∀ i : Fin 24, RowGood (36 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk37 : ∀ i : Fin 24, RowGood (37 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk38 : ∀ i : Fin 24, RowGood (38 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk39 : ∀ i : Fin 24, RowGood (39 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk40 : ∀ i : Fin 24, RowGood (40 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk41 : ∀ i : Fin 24, RowGood (41 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk42 : ∀ i : Fin 24, RowGood (42 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk43 : ∀ i : Fin 24, RowGood (43 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowChunk44 : ∀ i : Fin 24, RowGood (44 * 24 + i.val) := by
  unfold RowGood
  decide +kernel

theorem rowBlock4 : ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((4 * 9 + q.val) * 24 + i.val) := by
  intro q
  fin_cases q
  · exact rowChunk36
  · exact rowChunk37
  · exact rowChunk38
  · exact rowChunk39
  · exact rowChunk40
  · exact rowChunk41
  · exact rowChunk42
  · exact rowChunk43
  · exact rowChunk44

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
