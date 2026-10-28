module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeData
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.Slots

/-!
# Contract for one native matrix code

Every determinant-one code must have both literal right-generator edges,
together with bounds on all source row indices. The finite checks enumerate
all 19683 codes, including the codes skipped by the determinant test.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

@[expose] def NativeGood (c : Matrix.PSL3Three.MatrixCode) : Prop :=
  Matrix.PSL3Three.codeDet c = 1 →
    packedIndices (Matrix.PSL3Three.matrixCodeEquiv (Matrix.PSL3Three.decodeMatrix c * nativeA.val)) =
      mapSlots stepA 16 (packedIndices c) ∧
    packedIndices (Matrix.PSL3Three.matrixCodeEquiv (Matrix.PSL3Three.decodeMatrix c * nativeB.val)) =
      mapSlots stepB 16 (packedIndices c) ∧
    boundedSlots 16 (packedIndices c) = true


end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
