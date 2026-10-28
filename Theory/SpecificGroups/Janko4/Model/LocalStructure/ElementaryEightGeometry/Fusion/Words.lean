module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftWords

/-!
# A native word for fusion of the displayed elementary eights

The literal max1 word is shared by concatenation. The conjugator includes its
left kernel correction in the original eleven-bit coordinates.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
namespace FusionWords
def literalWord : List (Fin 4) := [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 2, 3, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 3, 3, 0, 3, 0]
def w0 : List (Fin 4) := [0]
def w1 : List (Fin 4) := [1]
def w2 : List (Fin 4) := [2]
def w3 : List (Fin 4) := [3]
def w4 : List (Fin 4) := w3 ++ w0
def w5 : List (Fin 4) := w1 ++ w2
def w6 : List (Fin 4) := w1 ++ w0
def w7 : List (Fin 4) := w3 ++ w2
def w8 : List (Fin 4) := w4 ++ w4
def w9 : List (Fin 4) := w5 ++ w5
def w10 : List (Fin 4) := w6 ++ w6
def w11 : List (Fin 4) := w7 ++ w7
def w12 : List (Fin 4) := w6 ++ w8
def w13 : List (Fin 4) := w4 ++ w10
def w14 : List (Fin 4) := w9 ++ w7
def w15 : List (Fin 4) := w12 ++ w13
def w16 : List (Fin 4) := w6 ++ w13
def w17 : List (Fin 4) := w14 ++ w5
def w18 : List (Fin 4) := w3 ++ w4
def w19 : List (Fin 4) := w6 ++ w4
def w20 : List (Fin 4) := w5 ++ w7
def w21 : List (Fin 4) := w8 ++ w15
def w22 : List (Fin 4) := w21 ++ w16
def w23 : List (Fin 4) := w22 ++ w6
def w24 : List (Fin 4) := w23 ++ w17
def w25 : List (Fin 4) := w24 ++ w18
def w26 : List (Fin 4) := w25 ++ w15
def w27 : List (Fin 4) := w26 ++ w5
def w28 : List (Fin 4) := w27 ++ w11
def w29 : List (Fin 4) := w28 ++ w11
def w30 : List (Fin 4) := w29 ++ w9
def w31 : List (Fin 4) := w30 ++ w11
def w32 : List (Fin 4) := w31 ++ w5
def w33 : List (Fin 4) := w32 ++ w8
def w34 : List (Fin 4) := w33 ++ w8
def w35 : List (Fin 4) := w34 ++ w19
def w36 : List (Fin 4) := w35 ++ w16
def w37 : List (Fin 4) := w36 ++ w10
def w38 : List (Fin 4) := w37 ++ w12
def w39 : List (Fin 4) := w38 ++ w4
def w40 : List (Fin 4) := w39 ++ w1
def w41 : List (Fin 4) := w40 ++ w20
def w42 : List (Fin 4) := w41 ++ w9
def w43 : List (Fin 4) := w42 ++ w14
def w44 : List (Fin 4) := w43 ++ w9
def w45 : List (Fin 4) := w44 ++ w17
def w46 : List (Fin 4) := w45 ++ w11
def w47 : List (Fin 4) := w46 ++ w7
def w48 : List (Fin 4) := w47 ++ w9
def w49 : List (Fin 4) := w48 ++ w18
def w50 : List (Fin 4) := w49 ++ w12
def w51 : List (Fin 4) := w50 ++ w12
def w52 : List (Fin 4) := w51 ++ w19
def w53 : List (Fin 4) := w52 ++ w1
def w54 : List (Fin 4) := w53 ++ w9
def w55 : List (Fin 4) := w54 ++ w20
def w56 : List (Fin 4) := w55 ++ w5
def w57 : List (Fin 4) := w56 ++ w3
def w58 : List (Fin 4) := w57 ++ w8
theorem finalWord_eq : w58 = literalWord := by decide +kernel
end FusionWords

/-- An actual element of the original Mathieu local subgroup. -/
def localFusion : SylowCore.Local :=
  nativeMask 16 * Theory.GroupTheory.evalWord nativeAlphabet FusionWords.literalWord

/-- The same conjugator in the original J4 carrier. -/
def nativeFusion : Model := (localFusion : SylowCore.Local)

end Janko4.LocalStructure.ElementaryEightGeometry
