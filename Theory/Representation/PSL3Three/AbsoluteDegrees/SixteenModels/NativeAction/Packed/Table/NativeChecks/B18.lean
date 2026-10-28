module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 18

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk162 : ∀ i : Fin 81, NativeGood (⟨162 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk163 : ∀ i : Fin 81, NativeGood (⟨163 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk164 : ∀ i : Fin 81, NativeGood (⟨164 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk165 : ∀ i : Fin 81, NativeGood (⟨165 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk166 : ∀ i : Fin 81, NativeGood (⟨166 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk167 : ∀ i : Fin 81, NativeGood (⟨167 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk168 : ∀ i : Fin 81, NativeGood (⟨168 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk169 : ∀ i : Fin 81, NativeGood (⟨169 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk170 : ∀ i : Fin 81, NativeGood (⟨170 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock18 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(18 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk162
  · exact nativeChunk163
  · exact nativeChunk164
  · exact nativeChunk165
  · exact nativeChunk166
  · exact nativeChunk167
  · exact nativeChunk168
  · exact nativeChunk169
  · exact nativeChunk170

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
