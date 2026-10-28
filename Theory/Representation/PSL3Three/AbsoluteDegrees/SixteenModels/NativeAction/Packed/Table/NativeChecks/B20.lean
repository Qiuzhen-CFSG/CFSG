module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 20

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk180 : ∀ i : Fin 81, NativeGood (⟨180 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk181 : ∀ i : Fin 81, NativeGood (⟨181 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk182 : ∀ i : Fin 81, NativeGood (⟨182 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk183 : ∀ i : Fin 81, NativeGood (⟨183 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk184 : ∀ i : Fin 81, NativeGood (⟨184 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk185 : ∀ i : Fin 81, NativeGood (⟨185 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk186 : ∀ i : Fin 81, NativeGood (⟨186 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk187 : ∀ i : Fin 81, NativeGood (⟨187 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk188 : ∀ i : Fin 81, NativeGood (⟨188 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock20 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(20 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk180
  · exact nativeChunk181
  · exact nativeChunk182
  · exact nativeChunk183
  · exact nativeChunk184
  · exact nativeChunk185
  · exact nativeChunk186
  · exact nativeChunk187
  · exact nativeChunk188

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
