module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Data

/-!
# Binary-polynomial arithmetic for the native degree-sixteen action

Codes are four binary digits. Addition is XOR; multiplication reduces by
`X⁴+X+1`, using the displayed multiplication-by-X table. These operations
are deliberately separate from the arithmetic of `Fin 16` modulo sixteen.
`matrixMul` is ordinary row-by-column multiplication in this encoding.

The coefficient convention and numerical matrices are the attributed ATLAS
L33G1-f16r16aB0 data in `SixteenModels.Data`. Evaluation and the genuine native
action are proved in the separate `Evaluation` and `Transport` modules.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction

@[expose] def addCode (a b : Fin 16) : Fin 16 := ⟨a.val ^^^ b.val, by
  have h : ∀ a b : Fin 16, a.val ^^^ b.val < 16 := by decide
  exact h a b⟩

@[expose] def shiftCode : Fin 16 → Fin 16 :=
  ![0,2,4,6,8,10,12,14,3,1,7,5,11,9,15,13]

@[expose] def mulCode (a : Fin 16) : Fin 16 → Fin 16 :=
  let a2 := shiftCode a
  let a4 := shiftCode a2
  let a8 := shiftCode a4
  ![0,a,a2,addCode a2 a,a4,addCode a4 a,addCode a4 a2,
    addCode (addCode a4 a2) a,a8,addCode a8 a,addCode a8 a2,
    addCode (addCode a8 a2) a,addCode a8 a4,addCode (addCode a8 a4) a,
    addCode (addCode a8 a4) a2,addCode (addCode (addCode a8 a4) a2) a]

abbrev CodeMatrix := Matrix (Fin 16) (Fin 16) (Fin 16)

@[expose] def sumCode : List (Fin 16) → Fin 16
  | [] => 0
  | x :: xs => addCode x (sumCode xs)

@[expose] def matrixMul (A B : CodeMatrix) : CodeMatrix :=
  fun i j => sumCode (List.ofFn (fun k : Fin 16 => mulCode (A i k) (B k j)))

@[expose] def matrixOne : CodeMatrix := fun i j => if i = j then 1 else 0

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction
