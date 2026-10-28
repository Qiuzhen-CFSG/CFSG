module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.EdgeTable

/-!
# Packed rows for the finite native-action certificate

A natural number stores sixteen base-sixteen entries, one nibble per column.
The shift masks apply multiplication by X modulo X⁴+X+1 to all entries at once;
XOR adds rows. The two packed generators are checked against the published ATLAS
matrices, retaining their attribution in `SixteenModels.Data`.

Two independent obligations are exposed: `MultiplicationCorrect` proves the
packed arithmetic agrees with `Encoding.matrixMul`; `Certificate` supplies the
finite native right-edge table. Their proved adapter produces `EdgeTable`.
Neither obligation is assumed to have a witness.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

namespace Packed
abbrev Rows := Vector ℕ 16

@[expose] def digit (r : ℕ) (j : Fin 16) : Fin 16 :=
  ⟨r / 16 ^ j.val % 16, Nat.mod_lt _ (by decide)⟩

@[expose] def decode (x : Rows) : CodeMatrix := fun i j => digit (x.get i) j

@[expose] def shift (r : ℕ) : ℕ :=
  ((r &&& 8608480567731124087) <<< 1) ^^^
    (((r >>> 3) &&& 1229782938247303441) * 3)

/-- Multiply all sixteen nibbles by the four-bit scalar. -/
@[expose] def scale (a : Fin 16) (r : ℕ) : ℕ :=
  (if a.val.testBit 0 then r else 0) ^^^
  (if a.val.testBit 1 then shift r else 0) ^^^
  (if a.val.testBit 2 then shift (shift r) else 0) ^^^
  (if a.val.testBit 3 then shift (shift (shift r)) else 0)

/-- Read one nibble at a time; avoid rebuilding indexed lists and powers. -/
@[expose] def scan : ℕ → List ℕ → ℕ
  | _, [] => 0
  | r, y :: ys =>
      scale ⟨r % 16, Nat.mod_lt _ (by decide)⟩ y ^^^ scan (r / 16) ys

@[expose] def row (r : ℕ) (y : Rows) : ℕ := scan r y.toList

@[expose] def mul (x y : Rows) : Rows := Vector.ofFn (fun i => row (x.get i) y)

@[expose] def one : Rows := #v[1, 16, 256, 4096,
    65536, 1048576, 16777216, 268435456,
    4294967296, 68719476736, 1099511627776, 17592186044416,
    281474976710656, 4503599627370496, 72057594037927936, 1152921504606846976]

@[expose] def generatorA : Rows := #v[16, 1, 4096, 256,
    1048576, 65536, 4294967296, 68719476736,
    16777216, 268435456, 1103823376657, 4503599627370496,
    50021785611455225, 17592186044416, 6767415282554559234, 15270347697842138765]

@[expose] def generatorB : Rows := #v[256, 272, 257, 65536,
    16777216, 268435456, 4096, 1099511627776,
    17592186044416, 281474976710656, 1048576, 72057594037927936,
    1152921504606846976, 1088269856022338315, 4294967296, 68719476736]

theorem decode_one : decode one = matrixOne := by decide
theorem decode_generatorA : decode generatorA = codesA := by decide
theorem decode_generatorB : decode generatorB = codesB := by decide

/-- The independent packed-arithmetic correctness obligation. -/
@[expose] def MultiplicationCorrect : Prop :=
  ∀ x y : Rows, decode (mul x y) = matrixMul (decode x) (decode y)

/-- Only finite numerical equalities, with the literal native matrix codes. -/
structure Certificate where
  image : Matrix.PSL3Three.MatrixCode → Rows
  one : image (Matrix.PSL3Three.matrixCodeEquiv 1) = one
  rightA : ∀ c, Matrix.PSL3Three.codeDet c = 1 →
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeA.val)) = mul (image c) generatorA
  rightB : ∀ c, Matrix.PSL3Three.codeDet c = 1 →
    image (Matrix.PSL3Three.matrixCodeEquiv
      (Matrix.PSL3Three.decodeMatrix c * nativeB.val)) = mul (image c) generatorB

@[expose] def Certificate.toEdgeTable (h : MultiplicationCorrect) (E : Certificate) : EdgeTable where
  image c := decode (E.image c)
  one := by rw [E.one, decode_one]
  rightA c hc := by rw [E.rightA c hc, h, decode_generatorA]
  rightB c hc := by rw [E.rightB c hc, h, decode_generatorB]
end Packed

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
