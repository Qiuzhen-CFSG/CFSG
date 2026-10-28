module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 25

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk225 : ∀ i : Fin 81, NativeGood (⟨225 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk226 : ∀ i : Fin 81, NativeGood (⟨226 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk227 : ∀ i : Fin 81, NativeGood (⟨227 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk228 : ∀ i : Fin 81, NativeGood (⟨228 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk229 : ∀ i : Fin 81, NativeGood (⟨229 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk230 : ∀ i : Fin 81, NativeGood (⟨230 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk231 : ∀ i : Fin 81, NativeGood (⟨231 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk232 : ∀ i : Fin 81, NativeGood (⟨232 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk233 : ∀ i : Fin 81, NativeGood (⟨233 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock25 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(25 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk225
  · exact nativeChunk226
  · exact nativeChunk227
  · exact nativeChunk228
  · exact nativeChunk229
  · exact nativeChunk230
  · exact nativeChunk231
  · exact nativeChunk232
  · exact nativeChunk233

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
