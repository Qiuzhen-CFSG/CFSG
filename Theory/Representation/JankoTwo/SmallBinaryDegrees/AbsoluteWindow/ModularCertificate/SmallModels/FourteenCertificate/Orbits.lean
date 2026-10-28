module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Evaluation

import Mathlib.Tactic.FinCases

/-!
# The two rank-one orbit bases

Left words prepend a generator, and right words append a generator.
Each step is a checked product on a single column or row, preserving the
reversal convention of FourteenData.leftWords. The stated one-sided inverses
are checked in the order required by density_of_rankOne.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

def column (i : Fin 14) : CodeVector 14 := fun k => FourteenData.P k i

theorem left0_code : FourteenData.v = (column 0) :=
  checkVector_sound _ _ (by decide +kernel)

omit [CharP F 2] in
theorem left0_eval (t : F) (_ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 0)).mulVec (evalVector t FourteenData.v) = evalVector t (column 0) := by
  change (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      []).mulVec (evalVector t FourteenData.v) = _
  rw [word_nil, Matrix.one_mulVec]
  exact congrArg (evalVector t) left0_code

theorem left1_code : codeMulVec FourteenData.A (column 0) = (column 1) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left1_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 1)).mulVec (evalVector t FourteenData.v) = evalVector t (column 1) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 0) (column 1) false (FourteenData.leftWords 0) (left0_eval t ht) left1_code

theorem left2_code : codeMulVec FourteenData.B (column 0) = (column 2) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left2_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 2)).mulVec (evalVector t FourteenData.v) = evalVector t (column 2) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 0) (column 2) true (FourteenData.leftWords 0) (left0_eval t ht) left2_code

theorem left3_code : codeMulVec FourteenData.B (column 1) = (column 3) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left3_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 3)).mulVec (evalVector t FourteenData.v) = evalVector t (column 3) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 1) (column 3) true (FourteenData.leftWords 1) (left1_eval t ht) left3_code

theorem left4_code : codeMulVec FourteenData.A (column 2) = (column 4) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left4_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 4)).mulVec (evalVector t FourteenData.v) = evalVector t (column 4) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 2) (column 4) false (FourteenData.leftWords 2) (left2_eval t ht) left4_code

theorem left5_code : codeMulVec FourteenData.B (column 2) = (column 5) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left5_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 5)).mulVec (evalVector t FourteenData.v) = evalVector t (column 5) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 2) (column 5) true (FourteenData.leftWords 2) (left2_eval t ht) left5_code

theorem left6_code : codeMulVec FourteenData.A (column 3) = (column 6) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left6_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 6)).mulVec (evalVector t FourteenData.v) = evalVector t (column 6) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 3) (column 6) false (FourteenData.leftWords 3) (left3_eval t ht) left6_code

theorem left7_code : codeMulVec FourteenData.B (column 3) = (column 7) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left7_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 7)).mulVec (evalVector t FourteenData.v) = evalVector t (column 7) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 3) (column 7) true (FourteenData.leftWords 3) (left3_eval t ht) left7_code

theorem left8_code : codeMulVec FourteenData.B (column 4) = (column 8) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left8_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 8)).mulVec (evalVector t FourteenData.v) = evalVector t (column 8) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 4) (column 8) true (FourteenData.leftWords 4) (left4_eval t ht) left8_code

theorem left9_code : codeMulVec FourteenData.A (column 5) = (column 9) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left9_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 9)).mulVec (evalVector t FourteenData.v) = evalVector t (column 9) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 5) (column 9) false (FourteenData.leftWords 5) (left5_eval t ht) left9_code

theorem left10_code : codeMulVec FourteenData.B (column 6) = (column 10) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left10_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 10)).mulVec (evalVector t FourteenData.v) = evalVector t (column 10) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 6) (column 10) true (FourteenData.leftWords 6) (left6_eval t ht) left10_code

theorem left11_code : codeMulVec FourteenData.A (column 7) = (column 11) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left11_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 11)).mulVec (evalVector t FourteenData.v) = evalVector t (column 11) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 7) (column 11) false (FourteenData.leftWords 7) (left7_eval t ht) left11_code

theorem left12_code : codeMulVec FourteenData.A (column 8) = (column 12) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left12_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 12)).mulVec (evalVector t FourteenData.v) = evalVector t (column 12) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 8) (column 12) false (FourteenData.leftWords 8) (left8_eval t ht) left12_code

theorem left13_code : codeMulVec FourteenData.B (column 9) = (column 13) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left13_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords 13)).mulVec (evalVector t FourteenData.v) = evalVector t (column 13) := by
  exact left_step t ht FourteenData.A FourteenData.B FourteenData.v
    (column 9) (column 13) true (FourteenData.leftWords 9) (left9_eval t ht) left13_code

theorem left_orbits (t : F) (ht : t ^ 2 = t + 1) (i : Fin 14) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      (FourteenData.leftWords i)).mulVec (evalVector t FourteenData.v) =
        fun k => evalMatrix t FourteenData.P k i := by
  fin_cases i
  · exact left0_eval t ht
  · exact left1_eval t ht
  · exact left2_eval t ht
  · exact left3_eval t ht
  · exact left4_eval t ht
  · exact left5_eval t ht
  · exact left6_eval t ht
  · exact left7_eval t ht
  · exact left8_eval t ht
  · exact left9_eval t ht
  · exact left10_eval t ht
  · exact left11_eval t ht
  · exact left12_eval t ht
  · exact left13_eval t ht

theorem right0_code : FourteenData.lam = (FourteenData.Q 0) :=
  checkVector_sound _ _ (by decide +kernel)

omit [CharP F 2] in
theorem right0_eval (t : F) (_ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 0)) = evalVector t (FourteenData.Q 0) := by
  change Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        []) = _
  rw [word_nil, Matrix.vecMul_one]
  exact congrArg (evalVector t) right0_code

theorem right1_code : codeVecMul (FourteenData.Q 0) FourteenData.A = (FourteenData.Q 1) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right1_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 1)) = evalVector t (FourteenData.Q 1) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 0) (FourteenData.Q 1) (FourteenData.rightWords 0) false (right0_eval t ht) right1_code

theorem right2_code : codeVecMul (FourteenData.Q 0) FourteenData.B = (FourteenData.Q 2) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right2_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 2)) = evalVector t (FourteenData.Q 2) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 0) (FourteenData.Q 2) (FourteenData.rightWords 0) true (right0_eval t ht) right2_code

theorem right3_code : codeVecMul (FourteenData.Q 2) FourteenData.A = (FourteenData.Q 3) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right3_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 3)) = evalVector t (FourteenData.Q 3) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 2) (FourteenData.Q 3) (FourteenData.rightWords 2) false (right2_eval t ht) right3_code

theorem right4_code : codeVecMul (FourteenData.Q 3) FourteenData.B = (FourteenData.Q 4) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right4_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 4)) = evalVector t (FourteenData.Q 4) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 3) (FourteenData.Q 4) (FourteenData.rightWords 3) true (right3_eval t ht) right4_code

theorem right5_code : codeVecMul (FourteenData.Q 4) FourteenData.A = (FourteenData.Q 5) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right5_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 5)) = evalVector t (FourteenData.Q 5) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 4) (FourteenData.Q 5) (FourteenData.rightWords 4) false (right4_eval t ht) right5_code

theorem right6_code : codeVecMul (FourteenData.Q 5) FourteenData.B = (FourteenData.Q 6) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right6_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 6)) = evalVector t (FourteenData.Q 6) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 5) (FourteenData.Q 6) (FourteenData.rightWords 5) true (right5_eval t ht) right6_code

theorem right7_code : codeVecMul (FourteenData.Q 6) FourteenData.A = (FourteenData.Q 7) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right7_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 7)) = evalVector t (FourteenData.Q 7) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 6) (FourteenData.Q 7) (FourteenData.rightWords 6) false (right6_eval t ht) right7_code

theorem right8_code : codeVecMul (FourteenData.Q 6) FourteenData.B = (FourteenData.Q 8) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right8_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 8)) = evalVector t (FourteenData.Q 8) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 6) (FourteenData.Q 8) (FourteenData.rightWords 6) true (right6_eval t ht) right8_code

theorem right9_code : codeVecMul (FourteenData.Q 7) FourteenData.B = (FourteenData.Q 9) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right9_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 9)) = evalVector t (FourteenData.Q 9) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 7) (FourteenData.Q 9) (FourteenData.rightWords 7) true (right7_eval t ht) right9_code

theorem right10_code : codeVecMul (FourteenData.Q 9) FourteenData.B = (FourteenData.Q 10) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right10_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 10)) = evalVector t (FourteenData.Q 10) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 9) (FourteenData.Q 10) (FourteenData.rightWords 9) true (right9_eval t ht) right10_code

theorem right11_code : codeVecMul (FourteenData.Q 10) FourteenData.A = (FourteenData.Q 11) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right11_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 11)) = evalVector t (FourteenData.Q 11) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 10) (FourteenData.Q 11) (FourteenData.rightWords 10) false (right10_eval t ht) right11_code

theorem right12_code : codeVecMul (FourteenData.Q 11) FourteenData.B = (FourteenData.Q 12) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right12_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 12)) = evalVector t (FourteenData.Q 12) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 11) (FourteenData.Q 12) (FourteenData.rightWords 11) true (right11_eval t ht) right12_code

theorem right13_code : codeVecMul (FourteenData.Q 12) FourteenData.B = (FourteenData.Q 13) :=
  checkVector_sound _ _ (by decide +kernel)

theorem right13_eval (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords 13)) = evalVector t (FourteenData.Q 13) := by
  exact right_step t ht FourteenData.A FourteenData.B FourteenData.lam
    (FourteenData.Q 12) (FourteenData.Q 13) (FourteenData.rightWords 12) true (right12_eval t ht) right13_code

theorem right_orbits (t : F) (ht : t ^ 2 = t + 1) (i : Fin 14) :
    Matrix.vecMul (evalVector t FourteenData.lam)
      (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
        (FourteenData.rightWords i)) = evalMatrix t FourteenData.Q i := by
  fin_cases i
  · exact right0_eval t ht
  · exact right1_eval t ht
  · exact right2_eval t ht
  · exact right3_eval t ht
  · exact right4_eval t ht
  · exact right5_eval t ht
  · exact right6_eval t ht
  · exact right7_eval t ht
  · exact right8_eval t ht
  · exact right9_eval t ht
  · exact right10_eval t ht
  · exact right11_eval t ht
  · exact right12_eval t ht
  · exact right13_eval t ht

theorem left_inverse_code : codeProduct FourteenData.P FourteenData.Pi = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem left_inverse (t : F) (ht : t ^ 2 = t + 1) :
    evalMatrix t FourteenData.P * evalMatrix t FourteenData.Pi = 1 :=
  (product_eq t ht _ _ _ left_inverse_code).trans (eval_one t)

theorem right_inverse_code : codeProduct FourteenData.Qi FourteenData.Q = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem right_inverse (t : F) (ht : t ^ 2 = t + 1) :
    evalMatrix t FourteenData.Qi * evalMatrix t FourteenData.Q = 1 :=
  (product_eq t ht _ _ _ right_inverse_code).trans (eval_one t)


end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
