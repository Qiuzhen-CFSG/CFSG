module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 23

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk207 : ∀ i : Fin 81, NativeGood (⟨207 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk208 : ∀ i : Fin 81, NativeGood (⟨208 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk209 : ∀ i : Fin 81, NativeGood (⟨209 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk210 : ∀ i : Fin 81, NativeGood (⟨210 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk211 : ∀ i : Fin 81, NativeGood (⟨211 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk212 : ∀ i : Fin 81, NativeGood (⟨212 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk213 : ∀ i : Fin 81, NativeGood (⟨213 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk214 : ∀ i : Fin 81, NativeGood (⟨214 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk215 : ∀ i : Fin 81, NativeGood (⟨215 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock23 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(23 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk207
  · exact nativeChunk208
  · exact nativeChunk209
  · exact nativeChunk210
  · exact nativeChunk211
  · exact nativeChunk212
  · exact nativeChunk213
  · exact nativeChunk214
  · exact nativeChunk215

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
