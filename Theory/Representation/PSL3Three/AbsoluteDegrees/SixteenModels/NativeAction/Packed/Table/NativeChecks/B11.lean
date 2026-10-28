module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 11

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk99 : ∀ i : Fin 81, NativeGood (⟨99 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk100 : ∀ i : Fin 81, NativeGood (⟨100 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk101 : ∀ i : Fin 81, NativeGood (⟨101 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk102 : ∀ i : Fin 81, NativeGood (⟨102 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk103 : ∀ i : Fin 81, NativeGood (⟨103 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk104 : ∀ i : Fin 81, NativeGood (⟨104 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk105 : ∀ i : Fin 81, NativeGood (⟨105 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk106 : ∀ i : Fin 81, NativeGood (⟨106 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk107 : ∀ i : Fin 81, NativeGood (⟨107 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock11 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(11 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk99
  · exact nativeChunk100
  · exact nativeChunk101
  · exact nativeChunk102
  · exact nativeChunk103
  · exact nativeChunk104
  · exact nativeChunk105
  · exact nativeChunk106
  · exact nativeChunk107

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
