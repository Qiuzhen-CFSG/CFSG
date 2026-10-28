module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 22

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk198 : ∀ i : Fin 81, NativeGood (⟨198 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk199 : ∀ i : Fin 81, NativeGood (⟨199 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk200 : ∀ i : Fin 81, NativeGood (⟨200 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk201 : ∀ i : Fin 81, NativeGood (⟨201 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk202 : ∀ i : Fin 81, NativeGood (⟨202 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk203 : ∀ i : Fin 81, NativeGood (⟨203 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk204 : ∀ i : Fin 81, NativeGood (⟨204 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk205 : ∀ i : Fin 81, NativeGood (⟨205 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk206 : ∀ i : Fin 81, NativeGood (⟨206 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock22 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(22 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk198
  · exact nativeChunk199
  · exact nativeChunk200
  · exact nativeChunk201
  · exact nativeChunk202
  · exact nativeChunk203
  · exact nativeChunk204
  · exact nativeChunk205
  · exact nativeChunk206

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
