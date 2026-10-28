module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 21

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk189 : ∀ i : Fin 81, NativeGood (⟨189 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk190 : ∀ i : Fin 81, NativeGood (⟨190 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk191 : ∀ i : Fin 81, NativeGood (⟨191 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk192 : ∀ i : Fin 81, NativeGood (⟨192 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk193 : ∀ i : Fin 81, NativeGood (⟨193 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk194 : ∀ i : Fin 81, NativeGood (⟨194 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk195 : ∀ i : Fin 81, NativeGood (⟨195 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk196 : ∀ i : Fin 81, NativeGood (⟨196 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk197 : ∀ i : Fin 81, NativeGood (⟨197 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock21 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(21 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk189
  · exact nativeChunk190
  · exact nativeChunk191
  · exact nativeChunk192
  · exact nativeChunk193
  · exact nativeChunk194
  · exact nativeChunk195
  · exact nativeChunk196
  · exact nativeChunk197

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
