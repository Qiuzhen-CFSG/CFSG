module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 19

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk171 : ∀ i : Fin 81, NativeGood (⟨171 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk172 : ∀ i : Fin 81, NativeGood (⟨172 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk173 : ∀ i : Fin 81, NativeGood (⟨173 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk174 : ∀ i : Fin 81, NativeGood (⟨174 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk175 : ∀ i : Fin 81, NativeGood (⟨175 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk176 : ∀ i : Fin 81, NativeGood (⟨176 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk177 : ∀ i : Fin 81, NativeGood (⟨177 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk178 : ∀ i : Fin 81, NativeGood (⟨178 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk179 : ∀ i : Fin 81, NativeGood (⟨179 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock19 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(19 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk171
  · exact nativeChunk172
  · exact nativeChunk173
  · exact nativeChunk174
  · exact nativeChunk175
  · exact nativeChunk176
  · exact nativeChunk177
  · exact nativeChunk178
  · exact nativeChunk179

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
