module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 24

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk216 : ∀ i : Fin 81, NativeGood (⟨216 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk217 : ∀ i : Fin 81, NativeGood (⟨217 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk218 : ∀ i : Fin 81, NativeGood (⟨218 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk219 : ∀ i : Fin 81, NativeGood (⟨219 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk220 : ∀ i : Fin 81, NativeGood (⟨220 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk221 : ∀ i : Fin 81, NativeGood (⟨221 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk222 : ∀ i : Fin 81, NativeGood (⟨222 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk223 : ∀ i : Fin 81, NativeGood (⟨223 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk224 : ∀ i : Fin 81, NativeGood (⟨224 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock24 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(24 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk216
  · exact nativeChunk217
  · exact nativeChunk218
  · exact nativeChunk219
  · exact nativeChunk220
  · exact nativeChunk221
  · exact nativeChunk222
  · exact nativeChunk223
  · exact nativeChunk224

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
