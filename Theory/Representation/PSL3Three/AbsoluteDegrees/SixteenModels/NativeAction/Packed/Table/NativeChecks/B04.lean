module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.Defs

/-!
# Native certificate batch 4

This batch uses trusted kernel reduction at the default resource limits.
It is consumed by `NativeChecks`, which proves complete coverage.
Data attribution and the reproducible generator are in `Table/source`.
-/

-- Keep these finite kernel checks sequential within this compilation unit.
set_option Elab.async false

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

theorem nativeChunk36 : ∀ i : Fin 81, NativeGood (⟨36 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk37 : ∀ i : Fin 81, NativeGood (⟨37 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk38 : ∀ i : Fin 81, NativeGood (⟨38 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk39 : ∀ i : Fin 81, NativeGood (⟨39 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk40 : ∀ i : Fin 81, NativeGood (⟨40 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk41 : ∀ i : Fin 81, NativeGood (⟨41 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk42 : ∀ i : Fin 81, NativeGood (⟨42 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk43 : ∀ i : Fin 81, NativeGood (⟨43 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeChunk44 : ∀ i : Fin 81, NativeGood (⟨44 * 81 + i.val, by omega⟩) := by
  unfold NativeGood
  decide +kernel

theorem nativeBlock4 : ∀ q : Fin 9, ∀ i : Fin 81,
    NativeGood (⟨(4 * 9 + q.val) * 81 + i.val, by omega⟩) := by
  intro q
  fin_cases q
  · exact nativeChunk36
  · exact nativeChunk37
  · exact nativeChunk38
  · exact nativeChunk39
  · exact nativeChunk40
  · exact nativeChunk41
  · exact nativeChunk42
  · exact nativeChunk43
  · exact nativeChunk44

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
