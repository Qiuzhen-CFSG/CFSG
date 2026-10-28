module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 26

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk234 : ∀ i : Fin 81, NativeGood (⟨234 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk235 : ∀ i : Fin 81, NativeGood (⟨235 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk236 : ∀ i : Fin 81, NativeGood (⟨236 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk237 : ∀ i : Fin 81, NativeGood (⟨237 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk238 : ∀ i : Fin 81, NativeGood (⟨238 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk239 : ∀ i : Fin 81, NativeGood (⟨239 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk240 : ∀ i : Fin 81, NativeGood (⟨240 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk241 : ∀ i : Fin 81, NativeGood (⟨241 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk242 : ∀ i : Fin 81, NativeGood (⟨242 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock26 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(26 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk234
  · exact nativeChunk235
  · exact nativeChunk236
  · exact nativeChunk237
  · exact nativeChunk238
  · exact nativeChunk239
  · exact nativeChunk240
  · exact nativeChunk241
  · exact nativeChunk242

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
