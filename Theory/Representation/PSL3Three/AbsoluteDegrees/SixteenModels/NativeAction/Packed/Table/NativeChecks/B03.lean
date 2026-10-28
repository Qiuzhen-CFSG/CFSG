module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 3

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk27 : ∀ i : Fin 81, NativeGood (⟨27 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk28 : ∀ i : Fin 81, NativeGood (⟨28 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk29 : ∀ i : Fin 81, NativeGood (⟨29 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk30 : ∀ i : Fin 81, NativeGood (⟨30 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk31 : ∀ i : Fin 81, NativeGood (⟨31 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk32 : ∀ i : Fin 81, NativeGood (⟨32 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk33 : ∀ i : Fin 81, NativeGood (⟨33 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk34 : ∀ i : Fin 81, NativeGood (⟨34 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk35 : ∀ i : Fin 81, NativeGood (⟨35 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock3 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(3 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk27
  · exact nativeChunk28
  · exact nativeChunk29
  · exact nativeChunk30
  · exact nativeChunk31
  · exact nativeChunk32
  · exact nativeChunk33
  · exact nativeChunk34
  · exact nativeChunk35

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
