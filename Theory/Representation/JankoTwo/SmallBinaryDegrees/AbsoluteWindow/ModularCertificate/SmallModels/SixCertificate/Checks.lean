module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Data

/-!
# Checked products for the degree-six Hall--Janko matrices

Each table below is a proposed intermediate value, verified by the sound Boolean
checker in Lean's kernel. Shared word suffixes, successive powers, the linear
combination T and Horner evaluation of q(T) keep every check small. The final
identities certify the five relations, rank-one factorization, literal orbit
words, inverse matrices and nonbinary trace.

Source: ATLAS J2G1-f4r6aB0 and the witnesses in ../source/README.md.
The reproducing generator is source/generate.py; it is not a proof oracle.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.SixCertificate
open Arithmetic

def codeWord : List Bool → CodeMatrix 6
  | [] => codeOne
  | s :: w => codeProduct (if s then SixData.B else SixData.A) (codeWord w)

def codePow (M : CodeMatrix 6) : ℕ → CodeMatrix 6
  | 0 => codeOne
  | n + 1 => codeProduct (codePow M n) M

def codeLin : List (List Bool) → List (Fin 4) → CodeMatrix 6
  | [], _ => codeZero
  | _, [] => codeZero
  | w :: ws, c :: cs => codeAdd (codeScale c (codeWord w)) (codeLin ws cs)

def codePoly : List (Fin 4) → CodeMatrix 6 → CodeMatrix 6
  | [], _ => codeZero
  | c :: cs, T => codeAdd (codeScale c codeOne) (codeProduct T (codePoly cs T))


theorem word_empty : codeWord [] = codeOne := rfl

def w1 : CodeMatrix 6 :=
  !![3, 3, 0, 0, 0, 0;
    1, 3, 0, 0, 0, 0;
    1, 1, 3, 3, 0, 0;
    2, 1, 1, 3, 0, 0;
    0, 3, 3, 3, 0, 2;
    3, 1, 3, 0, 3, 0]

theorem product_w1 : codeProduct SixData.A codeOne = w1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w1 : codeWord [false] = w1 := by
  change codeProduct SixData.A (codeWord []) = w1
  rw [word_empty]
  exact product_w1

def r1p1 : CodeMatrix 6 :=
  !![3, 3, 0, 0, 0, 0;
    1, 3, 0, 0, 0, 0;
    1, 1, 3, 3, 0, 0;
    2, 1, 1, 3, 0, 0;
    0, 3, 3, 3, 0, 2;
    3, 1, 3, 0, 3, 0]

theorem product_r1p1 : codeProduct codeOne w1 = r1p1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r1p1 : codePow w1 1 = r1p1 := by
  change codeProduct (codePow w1 0) w1 = r1p1
  exact product_r1p1

theorem product_r1p2 : codeProduct r1p1 w1 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r1p2 : codePow w1 2 = codeOne := by
  change codeProduct (codePow w1 1) w1 = codeOne
  rw [power_r1p1]
  exact product_r1p2

theorem relation_1 : codePow (codeWord [false]) 2 = codeOne := by
  rw [word_w1]
  exact power_r1p2

def w2 : CodeMatrix 6 :=
  !![2, 1, 3, 1, 3, 3;
    2, 1, 2, 1, 1, 2;
    2, 2, 3, 3, 1, 0;
    0, 0, 0, 0, 1, 1;
    3, 1, 3, 3, 2, 3;
    3, 1, 3, 2, 3, 2]

theorem product_w2 : codeProduct SixData.B codeOne = w2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w2 : codeWord [true] = w2 := by
  change codeProduct SixData.B (codeWord []) = w2
  rw [word_empty]
  exact product_w2

def r2p1 : CodeMatrix 6 :=
  !![2, 1, 3, 1, 3, 3;
    2, 1, 2, 1, 1, 2;
    2, 2, 3, 3, 1, 0;
    0, 0, 0, 0, 1, 1;
    3, 1, 3, 3, 2, 3;
    3, 1, 3, 2, 3, 2]

theorem product_r2p1 : codeProduct codeOne w2 = r2p1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r2p1 : codePow w2 1 = r2p1 := by
  change codeProduct (codePow w2 0) w2 = r2p1
  exact product_r2p1

def r2p2 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_r2p2 : codeProduct r2p1 w2 = r2p2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r2p2 : codePow w2 2 = r2p2 := by
  change codeProduct (codePow w2 1) w2 = r2p2
  rw [power_r2p1]
  exact product_r2p2

theorem product_r2p3 : codeProduct r2p2 w2 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r2p3 : codePow w2 3 = codeOne := by
  change codeProduct (codePow w2 2) w2 = codeOne
  rw [power_r2p2]
  exact product_r2p3

theorem relation_2 : codePow (codeWord [true]) 3 = codeOne := by
  rw [word_w2]
  exact power_r2p3

def w3 : CodeMatrix 6 :=
  !![0, 0, 3, 0, 1, 3;
    3, 2, 2, 2, 0, 2;
    1, 1, 3, 2, 2, 2;
    3, 1, 0, 0, 2, 0;
    1, 0, 2, 2, 2, 1;
    0, 0, 0, 2, 1, 2]

theorem product_w3 : codeProduct SixData.A w2 = w3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w3 : codeWord [false, true] = w3 := by
  change codeProduct SixData.A (codeWord [true]) = w3
  rw [word_w2]
  exact product_w3

def r3p1 : CodeMatrix 6 :=
  !![0, 0, 3, 0, 1, 3;
    3, 2, 2, 2, 0, 2;
    1, 1, 3, 2, 2, 2;
    3, 1, 0, 0, 2, 0;
    1, 0, 2, 2, 2, 1;
    0, 0, 0, 2, 1, 2]

theorem product_r3p1 : codeProduct codeOne w3 = r3p1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p1 : codePow w3 1 = r3p1 := by
  change codeProduct (codePow w3 0) w3 = r3p1
  exact product_r3p1

def r3p2 : CodeMatrix 6 :=
  !![2, 3, 0, 2, 0, 1;
    2, 3, 0, 3, 1, 1;
    3, 3, 0, 3, 2, 1;
    1, 2, 3, 1, 0, 2;
    1, 0, 1, 2, 3, 0;
    0, 2, 2, 1, 3, 2]

theorem product_r3p2 : codeProduct r3p1 w3 = r3p2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p2 : codePow w3 2 = r3p2 := by
  change codeProduct (codePow w3 1) w3 = r3p2
  rw [power_r3p1]
  exact product_r3p2

def r3p3 : CodeMatrix 6 :=
  !![3, 3, 0, 3, 0, 2;
    1, 2, 2, 1, 0, 3;
    2, 2, 0, 0, 0, 3;
    1, 1, 2, 1, 0, 2;
    3, 3, 1, 3, 1, 2;
    3, 0, 3, 2, 2, 0]

theorem product_r3p3 : codeProduct r3p2 w3 = r3p3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p3 : codePow w3 3 = r3p3 := by
  change codeProduct (codePow w3 2) w3 = r3p3
  rw [power_r3p2]
  exact product_r3p3

def r3p4 : CodeMatrix 6 :=
  !![0, 2, 3, 2, 0, 0;
    0, 0, 1, 1, 3, 2;
    1, 3, 2, 2, 1, 3;
    2, 1, 0, 2, 2, 1;
    0, 3, 2, 2, 0, 3;
    0, 1, 3, 2, 2, 1]

theorem product_r3p4 : codeProduct r3p3 w3 = r3p4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p4 : codePow w3 4 = r3p4 := by
  change codeProduct (codePow w3 3) w3 = r3p4
  rw [power_r3p3]
  exact product_r3p4

def r3p5 : CodeMatrix 6 :=
  !![3, 2, 1, 2, 2, 2;
    1, 0, 2, 0, 3, 2;
    0, 1, 1, 1, 0, 1;
    0, 0, 0, 3, 3, 3;
    1, 1, 0, 3, 3, 3;
    3, 3, 3, 2, 0, 3]

theorem product_r3p5 : codeProduct r3p4 w3 = r3p5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p5 : codePow w3 5 = r3p5 := by
  change codeProduct (codePow w3 4) w3 = r3p5
  rw [power_r3p4]
  exact product_r3p5

def r3p6 : CodeMatrix 6 :=
  !![3, 0, 1, 1, 3, 2;
    1, 2, 3, 1, 1, 0;
    1, 2, 1, 2, 1, 2;
    1, 3, 1, 0, 3, 2;
    2, 1, 0, 2, 2, 3;
    0, 0, 1, 1, 2, 3]

theorem product_r3p6 : codeProduct r3p5 w3 = r3p6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p6 : codePow w3 6 = r3p6 := by
  change codeProduct (codePow w3 5) w3 = r3p6
  rw [power_r3p5]
  exact product_r3p6

theorem product_r3p7 : codeProduct r3p6 w3 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r3p7 : codePow w3 7 = codeOne := by
  change codeProduct (codePow w3 6) w3 = codeOne
  rw [power_r3p6]
  exact product_r3p7

theorem relation_3 : codePow (codeWord [false, true]) 7 = codeOne := by
  rw [word_w3]
  exact power_r3p7

def w4 : CodeMatrix 6 :=
  !![0, 0, 0, 3, 3, 0;
    3, 1, 0, 0, 3, 2;
    1, 3, 2, 0, 0, 2;
    1, 0, 2, 0, 3, 3;
    0, 2, 1, 1, 3, 2;
    2, 3, 3, 1, 2, 1]

theorem product_w4 : codeProduct SixData.B w3 = w4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w4 : codeWord [true, false, true] = w4 := by
  change codeProduct SixData.B (codeWord [false, true]) = w4
  rw [word_w3]
  exact product_w4

def w5 : CodeMatrix 6 :=
  !![0, 0, 2, 1, 2, 2;
    3, 3, 1, 2, 1, 2;
    1, 2, 1, 0, 1, 2;
    2, 1, 2, 0, 1, 3;
    2, 2, 0, 3, 3, 1;
    1, 3, 0, 3, 1, 1]

theorem product_w5 : codeProduct SixData.B w4 = w5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w5 : codeWord [true, true, false, true] = w5 := by
  change codeProduct SixData.B (codeWord [true, false, true]) = w5
  rw [word_w4]
  exact product_w5

def w6 : CodeMatrix 6 :=
  !![2, 2, 2, 2, 2, 0;
    2, 2, 1, 0, 1, 3;
    1, 1, 1, 3, 3, 3;
    3, 2, 2, 0, 0, 1;
    2, 1, 1, 0, 1, 0;
    1, 3, 3, 3, 1, 1]

theorem product_w6 : codeProduct SixData.A w5 = w6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w6 : codeWord [false, true, true, false, true] = w6 := by
  change codeProduct SixData.A (codeWord [true, true, false, true]) = w6
  rw [word_w5]
  exact product_w6

def r4p1 : CodeMatrix 6 :=
  !![2, 2, 2, 2, 2, 0;
    2, 2, 1, 0, 1, 3;
    1, 1, 1, 3, 3, 3;
    3, 2, 2, 0, 0, 1;
    2, 1, 1, 0, 1, 0;
    1, 3, 3, 3, 1, 1]

theorem product_r4p1 : codeProduct codeOne w6 = r4p1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p1 : codePow w6 1 = r4p1 := by
  change codeProduct (codePow w6 0) w6 = r4p1
  exact product_r4p1

def r4p2 : CodeMatrix 6 :=
  !![0, 3, 2, 2, 2, 2;
    0, 2, 3, 2, 0, 1;
    1, 1, 2, 3, 0, 0;
    1, 3, 2, 3, 3, 1;
    2, 1, 2, 0, 0, 0;
    1, 3, 1, 3, 3, 2]

theorem product_r4p2 : codeProduct r4p1 w6 = r4p2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p2 : codePow w6 2 = r4p2 := by
  change codeProduct (codePow w6 1) w6 = r4p2
  rw [power_r4p1]
  exact product_r4p2

def r4p3 : CodeMatrix 6 :=
  !![3, 3, 1, 0, 2, 3;
    0, 0, 1, 1, 1, 0;
    0, 3, 0, 3, 2, 1;
    3, 0, 2, 0, 2, 1;
    3, 3, 0, 2, 3, 2;
    3, 1, 3, 0, 3, 0]

theorem product_r4p3 : codeProduct r4p2 w6 = r4p3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p3 : codePow w6 3 = r4p3 := by
  change codeProduct (codePow w6 2) w6 = r4p3
  rw [power_r4p2]
  exact product_r4p3

def r4p4 : CodeMatrix 6 :=
  !![1, 1, 3, 0, 0, 2;
    0, 2, 2, 3, 2, 2;
    1, 1, 3, 3, 0, 0;
    1, 2, 2, 3, 3, 0;
    2, 1, 3, 0, 3, 2;
    1, 3, 0, 3, 1, 1]

theorem product_r4p4 : codeProduct r4p3 w6 = r4p4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p4 : codePow w6 4 = r4p4 := by
  change codeProduct (codePow w6 3) w6 = r4p4
  rw [power_r4p3]
  exact product_r4p4

def r4p5 : CodeMatrix 6 :=
  !![1, 2, 1, 1, 3, 3;
    2, 3, 2, 0, 3, 1;
    1, 2, 1, 0, 1, 2;
    0, 1, 0, 3, 2, 3;
    1, 0, 3, 0, 1, 3;
    2, 0, 2, 1, 1, 0]

theorem product_r4p5 : codeProduct r4p4 w6 = r4p5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p5 : codePow w6 5 = r4p5 := by
  change codeProduct (codePow w6 4) w6 = r4p5
  rw [power_r4p4]
  exact product_r4p5

def r4p6 : CodeMatrix 6 :=
  !![1, 3, 2, 3, 3, 0;
    0, 0, 2, 1, 3, 2;
    0, 0, 1, 0, 0, 0;
    0, 3, 0, 2, 0, 3;
    0, 2, 2, 2, 2, 1;
    0, 2, 2, 2, 3, 0]

theorem product_r4p6 : codeProduct r4p5 w6 = r4p6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p6 : codePow w6 6 = r4p6 := by
  change codeProduct (codePow w6 5) w6 = r4p6
  rw [power_r4p5]
  exact product_r4p6

def r4p7 : CodeMatrix 6 :=
  !![2, 3, 1, 3, 3, 0;
    2, 2, 2, 0, 0, 2;
    1, 1, 1, 3, 3, 3;
    3, 0, 2, 2, 0, 3;
    2, 3, 2, 2, 0, 3;
    1, 1, 0, 1, 0, 2]

theorem product_r4p7 : codeProduct r4p6 w6 = r4p7 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p7 : codePow w6 7 = r4p7 := by
  change codeProduct (codePow w6 6) w6 = r4p7
  rw [power_r4p6]
  exact product_r4p7

def r4p8 : CodeMatrix 6 :=
  !![0, 1, 3, 0, 0, 2;
    0, 3, 2, 3, 2, 2;
    1, 1, 2, 3, 0, 0;
    1, 2, 2, 2, 3, 0;
    2, 1, 3, 0, 2, 2;
    1, 3, 0, 3, 1, 0]

theorem product_r4p8 : codeProduct r4p7 w6 = r4p8 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p8 : codePow w6 8 = r4p8 := by
  change codeProduct (codePow w6 7) w6 = r4p8
  rw [power_r4p7]
  exact product_r4p8

def r4p9 : CodeMatrix 6 :=
  !![3, 0, 3, 3, 1, 3;
    0, 1, 3, 0, 2, 2;
    0, 3, 0, 3, 2, 1;
    3, 3, 2, 3, 2, 2;
    3, 1, 2, 0, 0, 3;
    3, 3, 1, 2, 0, 1]

theorem product_r4p9 : codeProduct r4p8 w6 = r4p9 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p9 : codePow w6 9 = r4p9 := by
  change codeProduct (codePow w6 8) w6 = r4p9
  rw [power_r4p8]
  exact product_r4p9

def r4p10 : CodeMatrix 6 :=
  !![1, 0, 0, 1, 1, 2;
    0, 2, 1, 3, 3, 3;
    1, 1, 3, 3, 0, 0;
    1, 0, 2, 1, 3, 2;
    2, 3, 0, 2, 2, 1;
    1, 1, 3, 1, 0, 2]

theorem product_r4p10 : codeProduct r4p9 w6 = r4p10 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p10 : codePow w6 10 = r4p10 := by
  change codeProduct (codePow w6 9) w6 = r4p10
  rw [power_r4p9]
  exact product_r4p10

def r4p11 : CodeMatrix 6 :=
  !![1, 0, 0, 3, 1, 3;
    2, 2, 3, 1, 1, 2;
    1, 2, 1, 0, 1, 2;
    0, 0, 0, 2, 2, 2;
    1, 0, 2, 0, 3, 1;
    2, 0, 3, 1, 3, 2]

theorem product_r4p11 : codeProduct r4p10 w6 = r4p11 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p11 : codePow w6 11 = r4p11 := by
  change codeProduct (codePow w6 10) w6 = r4p11
  rw [power_r4p10]
  exact product_r4p11

theorem product_r4p12 : codeProduct r4p11 w6 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r4p12 : codePow w6 12 = codeOne := by
  change codeProduct (codePow w6 11) w6 = codeOne
  rw [power_r4p11]
  exact product_r4p12

theorem relation_4 : codePow (codeWord [false, true, true, false, true]) 12 = codeOne := by
  rw [word_w6]
  exact power_r4p12

def w7 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_w7 : codeProduct SixData.B w2 = w7 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w7 : codeWord [true, true] = w7 := by
  change codeProduct SixData.B (codeWord [true]) = w7
  rw [word_w2]
  exact product_w7

def w8 : CodeMatrix 6 :=
  !![0, 3, 3, 0, 3, 2;
    0, 0, 1, 3, 1, 0;
    1, 1, 3, 0, 1, 1;
    2, 0, 1, 3, 0, 1;
    3, 1, 0, 3, 3, 2;
    2, 3, 2, 0, 1, 2]

theorem product_w8 : codeProduct SixData.A w7 = w8 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w8 : codeWord [false, true, true] = w8 := by
  change codeProduct SixData.A (codeWord [true, true]) = w8
  rw [word_w7]
  exact product_w8

def w9 : CodeMatrix 6 :=
  !![2, 3, 2, 2, 2, 1;
    0, 3, 3, 3, 3, 1;
    1, 3, 2, 0, 3, 1;
    1, 2, 2, 3, 2, 0;
    2, 1, 3, 0, 2, 3;
    1, 3, 0, 0, 0, 2]

theorem product_w9 : codeProduct SixData.B w8 = w9 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w9 : codeWord [true, false, true, true] = w9 := by
  change codeProduct SixData.B (codeWord [false, true, true]) = w9
  rw [word_w8]
  exact product_w9

def w10 : CodeMatrix 6 :=
  !![1, 0, 3, 3, 3, 0;
    2, 1, 0, 0, 0, 2;
    2, 3, 1, 3, 2, 3;
    1, 0, 3, 2, 2, 2;
    2, 0, 2, 0, 1, 3;
    3, 0, 1, 2, 1, 3]

theorem product_w10 : codeProduct SixData.A w9 = w10 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w10 : codeWord [false, true, false, true, true] = w10 := by
  change codeProduct SixData.A (codeWord [true, false, true, true]) = w10
  rw [word_w9]
  exact product_w10

def w11 : CodeMatrix 6 :=
  !![3, 3, 3, 0, 2, 2;
    1, 0, 0, 1, 3, 3;
    1, 0, 2, 2, 0, 3;
    1, 0, 3, 2, 0, 0;
    2, 3, 3, 0, 3, 2;
    2, 3, 3, 0, 1, 0]

theorem product_w11 : codeProduct SixData.B w10 = w11 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w11 : codeWord [true, false, true, false, true, true] = w11 := by
  change codeProduct SixData.B (codeWord [false, true, false, true, true]) = w11
  rw [word_w10]
  exact product_w11

def w12 : CodeMatrix 6 :=
  !![2, 1, 3, 2, 1, 3;
    2, 3, 3, 0, 1, 3;
    1, 2, 1, 2, 1, 2;
    0, 0, 0, 0, 2, 2;
    1, 1, 2, 1, 0, 3;
    0, 1, 1, 3, 2, 1]

theorem product_w12 : codeProduct SixData.B w11 = w12 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w12 : codeWord [true, true, false, true, false, true, true] = w12 := by
  change codeProduct SixData.B (codeWord [true, false, true, false, true, true]) = w12
  rw [word_w11]
  exact product_w12

def w13 : CodeMatrix 6 :=
  !![0, 1, 0, 1, 0, 0;
    3, 3, 1, 2, 2, 1;
    3, 3, 3, 3, 2, 0;
    0, 3, 3, 1, 3, 1;
    2, 1, 3, 0, 2, 0;
    3, 2, 3, 3, 1, 2]

theorem product_w13 : codeProduct SixData.A w12 = w13 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w13 : codeWord [false, true, true, false, true, false, true, true] = w13 := by
  change codeProduct SixData.A (codeWord [true, true, false, true, false, true, true]) = w13
  rw [word_w12]
  exact product_w13

def w14 : CodeMatrix 6 :=
  !![2, 2, 0, 1, 2, 1;
    1, 1, 1, 1, 2, 3;
    1, 2, 1, 0, 2, 1;
    1, 3, 0, 3, 3, 2;
    0, 3, 2, 2, 1, 3;
    1, 3, 1, 0, 1, 0]

theorem product_w14 : codeProduct SixData.B w13 = w14 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w14 : codeWord [true, false, true, true, false, true, false, true, true] = w14 := by
  change codeProduct SixData.B (codeWord [false, true, true, false, true, false, true, true]) = w14
  rw [word_w13]
  exact product_w14

def w15 : CodeMatrix 6 :=
  !![2, 2, 3, 0, 0, 1;
    1, 1, 3, 2, 3, 3;
    3, 0, 2, 2, 3, 0;
    0, 2, 0, 1, 1, 1;
    1, 1, 2, 1, 0, 0;
    3, 3, 3, 3, 1, 1]

theorem product_w15 : codeProduct SixData.A w14 = w15 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w15 : codeWord [false, true, false, true, true, false, true, false, true, true] = w15 := by
  change codeProduct SixData.A (codeWord [true, false, true, true, false, true, false, true, true]) = w15
  rw [word_w14]
  exact product_w15

def w16 : CodeMatrix 6 :=
  !![1, 1, 0, 3, 3, 3;
    3, 0, 2, 0, 1, 2;
    2, 1, 3, 0, 0, 0;
    2, 2, 1, 2, 1, 1;
    2, 1, 1, 0, 1, 0;
    0, 1, 0, 3, 1, 0]

theorem product_w16 : codeProduct SixData.B w15 = w16 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w16 : codeWord [true, false, true, false, true, true, false, true, false, true, true] = w16 := by
  change codeProduct SixData.B (codeWord [false, true, false, true, true, false, true, false, true, true]) = w16
  rw [word_w15]
  exact product_w16

def w17 : CodeMatrix 6 :=
  !![1, 3, 1, 2, 1, 3;
    3, 1, 1, 3, 0, 2;
    2, 3, 3, 2, 1, 2;
    2, 2, 2, 0, 3, 0;
    2, 0, 0, 0, 2, 2;
    0, 3, 3, 2, 0, 0]

theorem product_w17 : codeProduct SixData.A w16 = w17 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w17 : codeWord [false, true, false, true, false, true, true, false, true, false, true, true] = w17 := by
  change codeProduct SixData.A (codeWord [true, false, true, false, true, true, false, true, false, true, true]) = w17
  rw [word_w16]
  exact product_w17

def r5p1 : CodeMatrix 6 :=
  !![1, 3, 1, 2, 1, 3;
    3, 1, 1, 3, 0, 2;
    2, 3, 3, 2, 1, 2;
    2, 2, 2, 0, 3, 0;
    2, 0, 0, 0, 2, 2;
    0, 3, 3, 2, 0, 0]

theorem product_r5p1 : codeProduct codeOne w17 = r5p1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p1 : codePow w17 1 = r5p1 := by
  change codeProduct (codePow w17 0) w17 = r5p1
  exact product_r5p1

def r5p2 : CodeMatrix 6 :=
  !![0, 2, 0, 3, 3, 2;
    3, 0, 1, 3, 0, 2;
    0, 2, 1, 3, 2, 3;
    1, 2, 1, 1, 1, 0;
    1, 0, 3, 0, 1, 2;
    0, 2, 2, 3, 2, 0]

theorem product_r5p2 : codeProduct r5p1 w17 = r5p2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p2 : codePow w17 2 = r5p2 := by
  change codeProduct (codePow w17 1) w17 = r5p2
  rw [power_r5p1]
  exact product_r5p2

def r5p3 : CodeMatrix 6 :=
  !![1, 2, 2, 2, 3, 2;
    0, 1, 0, 0, 0, 0;
    1, 2, 2, 2, 0, 2;
    2, 0, 2, 1, 1, 0;
    2, 0, 2, 0, 0, 0;
    0, 2, 2, 2, 3, 3]

theorem product_r5p3 : codeProduct r5p2 w17 = r5p3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p3 : codePow w17 3 = r5p3 := by
  change codeProduct (codePow w17 2) w17 = r5p3
  rw [power_r5p2]
  exact product_r5p3

def r5p4 : CodeMatrix 6 :=
  !![1, 2, 0, 3, 3, 2;
    3, 1, 1, 3, 0, 2;
    0, 2, 0, 3, 2, 3;
    1, 2, 1, 0, 1, 0;
    1, 0, 3, 0, 0, 2;
    0, 2, 2, 3, 2, 1]

theorem product_r5p4 : codeProduct r5p3 w17 = r5p4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p4 : codePow w17 4 = r5p4 := by
  change codeProduct (codePow w17 3) w17 = r5p4
  rw [power_r5p3]
  exact product_r5p4

def r5p5 : CodeMatrix 6 :=
  !![0, 1, 3, 0, 2, 1;
    3, 0, 1, 3, 0, 2;
    3, 1, 1, 0, 1, 0;
    0, 2, 0, 1, 2, 0;
    0, 0, 2, 0, 2, 2;
    0, 1, 1, 0, 3, 3]

theorem product_r5p5 : codeProduct r5p4 w17 = r5p5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p5 : codePow w17 5 = r5p5 := by
  change codeProduct (codePow w17 4) w17 = r5p5
  rw [power_r5p4]
  exact product_r5p5

theorem product_r5p6 : codeProduct r5p5 w17 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem power_r5p6 : codePow w17 6 = codeOne := by
  change codeProduct (codePow w17 5) w17 = codeOne
  rw [power_r5p5]
  exact product_r5p6

theorem relation_5 : codePow (codeWord [false, true, false, true, false, true, true, false, true, false, true, true]) 6 = codeOne := by
  rw [word_w17]
  exact power_r5p6

def w18 : CodeMatrix 6 :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem product_w18 : codeProduct SixData.B w7 = w18 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w18 : codeWord [true, true, true] = w18 := by
  change codeProduct SixData.B (codeWord [true, true]) = w18
  rw [word_w7]
  exact product_w18

def w19 : CodeMatrix 6 :=
  !![3, 3, 0, 0, 0, 0;
    1, 3, 0, 0, 0, 0;
    1, 1, 3, 3, 0, 0;
    2, 1, 1, 3, 0, 0;
    0, 3, 3, 3, 0, 2;
    3, 1, 3, 0, 3, 0]

theorem product_w19 : codeProduct SixData.A w18 = w19 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w19 : codeWord [false, true, true, true] = w19 := by
  change codeProduct SixData.A (codeWord [true, true, true]) = w19
  rw [word_w18]
  exact product_w19

def w20 : CodeMatrix 6 :=
  !![3, 1, 3, 3, 2, 1;
    1, 0, 2, 1, 1, 2;
    1, 3, 2, 3, 0, 2;
    3, 2, 0, 3, 3, 2;
    3, 3, 2, 1, 2, 3;
    2, 0, 3, 1, 1, 1]

theorem product_w20 : codeProduct SixData.B w19 = w20 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w20 : codeWord [true, false, true, true, true] = w20 := by
  change codeProduct SixData.B (codeWord [false, true, true, true]) = w20
  rw [word_w19]
  exact product_w20

def w21 : CodeMatrix 6 :=
  !![3, 0, 1, 1, 3, 2;
    1, 2, 3, 1, 1, 0;
    1, 2, 1, 2, 1, 2;
    1, 3, 1, 0, 3, 2;
    2, 1, 0, 2, 2, 3;
    0, 0, 1, 1, 2, 3]

theorem product_w21 : codeProduct SixData.B w20 = w21 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w21 : codeWord [true, true, false, true, true, true] = w21 := by
  change codeProduct SixData.B (codeWord [true, false, true, true, true]) = w21
  rw [word_w20]
  exact product_w21

def w22 : CodeMatrix 6 :=
  !![1, 1, 1, 0, 1, 1;
    0, 1, 3, 2, 0, 2;
    2, 1, 2, 1, 3, 2;
    2, 2, 3, 1, 3, 0;
    3, 2, 0, 0, 1, 1;
    1, 0, 3, 2, 1, 2]

theorem product_w22 : codeProduct SixData.A w21 = w22 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w22 : codeWord [false, true, true, false, true, true, true] = w22 := by
  change codeProduct SixData.A (codeWord [true, true, false, true, true, true]) = w22
  rw [word_w21]
  exact product_w22

def w23 : CodeMatrix 6 :=
  !![0, 3, 1, 1, 3, 3;
    2, 1, 0, 2, 3, 1;
    1, 0, 0, 3, 3, 1;
    2, 2, 3, 2, 0, 3;
    1, 3, 1, 3, 2, 3;
    1, 3, 1, 0, 1, 0]

theorem product_w23 : codeProduct SixData.B w22 = w23 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w23 : codeWord [true, false, true, true, false, true, true, true] = w23 := by
  change codeProduct SixData.B (codeWord [false, true, true, false, true, true, true]) = w23
  rw [word_w22]
  exact product_w23

def w24 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_w24 : codeProduct SixData.A w8 = w24 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w24 : codeWord [false, false, true, true] = w24 := by
  change codeProduct SixData.A (codeWord [false, true, true]) = w24
  rw [word_w8]
  exact product_w24

def w25 : CodeMatrix 6 :=
  !![0, 3, 3, 0, 3, 2;
    0, 0, 1, 3, 1, 0;
    1, 1, 3, 0, 1, 1;
    2, 0, 1, 3, 0, 1;
    3, 1, 0, 3, 3, 2;
    2, 3, 2, 0, 1, 2]

theorem product_w25 : codeProduct SixData.A w24 = w25 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w25 : codeWord [false, false, false, true, true] = w25 := by
  change codeProduct SixData.A (codeWord [false, false, true, true]) = w25
  rw [word_w24]
  exact product_w25

def w26 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_w26 : codeProduct SixData.A w25 = w26 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w26 : codeWord [false, false, false, false, true, true] = w26 := by
  change codeProduct SixData.A (codeWord [false, false, false, true, true]) = w26
  rw [word_w25]
  exact product_w26

def w27 : CodeMatrix 6 :=
  !![0, 3, 3, 0, 3, 2;
    0, 0, 1, 3, 1, 0;
    1, 1, 3, 0, 1, 1;
    2, 0, 1, 3, 0, 1;
    3, 1, 0, 3, 3, 2;
    2, 3, 2, 0, 1, 2]

theorem product_w27 : codeProduct SixData.A w26 = w27 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w27 : codeWord [false, false, false, false, false, true, true] = w27 := by
  change codeProduct SixData.A (codeWord [false, false, false, false, true, true]) = w27
  rw [word_w26]
  exact product_w27

def w28 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_w28 : codeProduct SixData.A w27 = w28 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w28 : codeWord [false, false, false, false, false, false, true, true] = w28 := by
  change codeProduct SixData.A (codeWord [false, false, false, false, false, true, true]) = w28
  rw [word_w27]
  exact product_w28

def w29 : CodeMatrix 6 :=
  !![3, 1, 3, 3, 2, 1;
    1, 0, 2, 1, 1, 2;
    1, 3, 2, 3, 0, 2;
    3, 2, 0, 3, 3, 2;
    3, 3, 2, 1, 2, 3;
    2, 0, 3, 1, 1, 1]

theorem product_w29 : codeProduct SixData.B w1 = w29 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w29 : codeWord [true, false] = w29 := by
  change codeProduct SixData.B (codeWord [false]) = w29
  rw [word_w1]
  exact product_w29

def w30 : CodeMatrix 6 :=
  !![1, 3, 3, 1, 2, 2;
    0, 1, 2, 0, 1, 0;
    3, 2, 0, 2, 1, 3;
    3, 0, 1, 1, 0, 3;
    1, 3, 1, 1, 3, 3;
    2, 3, 0, 2, 1, 2]

theorem product_w30 : codeProduct SixData.A w29 = w30 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w30 : codeWord [false, true, false] = w30 := by
  change codeProduct SixData.A (codeWord [true, false]) = w30
  rw [word_w29]
  exact product_w30

def w31 : CodeMatrix 6 :=
  !![3, 1, 3, 3, 2, 1;
    1, 0, 2, 1, 1, 2;
    1, 3, 2, 3, 0, 2;
    3, 2, 0, 3, 3, 2;
    3, 3, 2, 1, 2, 3;
    2, 0, 3, 1, 1, 1]

theorem product_w31 : codeProduct SixData.A w30 = w31 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w31 : codeWord [false, false, true, false] = w31 := by
  change codeProduct SixData.A (codeWord [false, true, false]) = w31
  rw [word_w30]
  exact product_w31

def w32 : CodeMatrix 6 :=
  !![1, 3, 3, 1, 2, 2;
    0, 1, 2, 0, 1, 0;
    3, 2, 0, 2, 1, 3;
    3, 0, 1, 1, 0, 3;
    1, 3, 1, 1, 3, 3;
    2, 3, 0, 2, 1, 2]

theorem product_w32 : codeProduct SixData.A w31 = w32 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w32 : codeWord [false, false, false, true, false] = w32 := by
  change codeProduct SixData.A (codeWord [false, false, true, false]) = w32
  rw [word_w31]
  exact product_w32

def w33 : CodeMatrix 6 :=
  !![3, 1, 3, 3, 2, 1;
    1, 0, 2, 1, 1, 2;
    1, 3, 2, 3, 0, 2;
    3, 2, 0, 3, 3, 2;
    3, 3, 2, 1, 2, 3;
    2, 0, 3, 1, 1, 1]

theorem product_w33 : codeProduct SixData.A w32 = w33 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w33 : codeWord [false, false, false, false, true, false] = w33 := by
  change codeProduct SixData.A (codeWord [false, false, false, true, false]) = w33
  rw [word_w32]
  exact product_w33

def w34 : CodeMatrix 6 :=
  !![3, 0, 1, 1, 3, 2;
    1, 2, 3, 1, 1, 0;
    1, 2, 1, 2, 1, 2;
    1, 3, 1, 0, 3, 2;
    2, 1, 0, 2, 2, 3;
    0, 0, 1, 1, 2, 3]

theorem product_w34 : codeProduct SixData.B w33 = w34 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w34 : codeWord [true, false, false, false, false, true, false] = w34 := by
  change codeProduct SixData.B (codeWord [false, false, false, false, true, false]) = w34
  rw [word_w33]
  exact product_w34

def w35 : CodeMatrix 6 :=
  !![2, 3, 0, 2, 0, 1;
    2, 3, 0, 3, 1, 1;
    3, 3, 0, 3, 2, 1;
    1, 2, 3, 1, 0, 2;
    1, 0, 1, 2, 3, 0;
    0, 2, 2, 1, 3, 2]

theorem product_w35 : codeProduct SixData.A w4 = w35 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w35 : codeWord [false, true, false, true] = w35 := by
  change codeProduct SixData.A (codeWord [true, false, true]) = w35
  rw [word_w4]
  exact product_w35

def w36 : CodeMatrix 6 :=
  !![0, 0, 0, 3, 3, 0;
    3, 1, 0, 0, 3, 2;
    1, 3, 2, 0, 0, 2;
    1, 0, 2, 0, 3, 3;
    0, 2, 1, 1, 3, 2;
    2, 3, 3, 1, 2, 1]

theorem product_w36 : codeProduct SixData.A w35 = w36 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w36 : codeWord [false, false, true, false, true] = w36 := by
  change codeProduct SixData.A (codeWord [false, true, false, true]) = w36
  rw [word_w35]
  exact product_w36

def w37 : CodeMatrix 6 :=
  !![0, 0, 2, 1, 2, 2;
    3, 3, 1, 2, 1, 2;
    1, 2, 1, 0, 1, 2;
    2, 1, 2, 0, 1, 3;
    2, 2, 0, 3, 3, 1;
    1, 3, 0, 3, 1, 1]

theorem product_w37 : codeProduct SixData.B w36 = w37 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w37 : codeWord [true, false, false, true, false, true] = w37 := by
  change codeProduct SixData.B (codeWord [false, false, true, false, true]) = w37
  rw [word_w36]
  exact product_w37

def w38 : CodeMatrix 6 :=
  !![2, 2, 2, 2, 2, 0;
    2, 2, 1, 0, 1, 3;
    1, 1, 1, 3, 3, 3;
    3, 2, 2, 0, 0, 1;
    2, 1, 1, 0, 1, 0;
    1, 3, 3, 3, 1, 1]

theorem product_w38 : codeProduct SixData.A w37 = w38 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w38 : codeWord [false, true, false, false, true, false, true] = w38 := by
  change codeProduct SixData.A (codeWord [true, false, false, true, false, true]) = w38
  rw [word_w37]
  exact product_w38

def w39 : CodeMatrix 6 :=
  !![2, 1, 3, 1, 3, 3;
    2, 1, 2, 1, 1, 2;
    2, 2, 3, 3, 1, 0;
    0, 0, 0, 0, 1, 1;
    3, 1, 3, 3, 2, 3;
    3, 1, 3, 2, 3, 2]

theorem product_w39 : codeProduct SixData.A w3 = w39 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w39 : codeWord [false, false, true] = w39 := by
  change codeProduct SixData.A (codeWord [false, true]) = w39
  rw [word_w3]
  exact product_w39

def w40 : CodeMatrix 6 :=
  !![0, 2, 1, 2, 1, 1;
    0, 3, 0, 2, 0, 2;
    2, 0, 3, 1, 1, 2;
    0, 0, 0, 1, 1, 1;
    1, 2, 1, 0, 2, 3;
    1, 2, 1, 1, 2, 3]

theorem product_w40 : codeProduct SixData.B w39 = w40 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w40 : codeWord [true, false, false, true] = w40 := by
  change codeProduct SixData.B (codeWord [false, false, true]) = w40
  rw [word_w39]
  exact product_w40

def w41 : CodeMatrix 6 :=
  !![0, 3, 3, 0, 3, 2;
    0, 0, 1, 3, 1, 0;
    1, 1, 3, 0, 1, 1;
    2, 0, 1, 3, 0, 1;
    3, 1, 0, 3, 3, 2;
    2, 3, 2, 0, 1, 2]

theorem product_w41 : codeProduct SixData.A w40 = w41 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w41 : codeWord [false, true, false, false, true] = w41 := by
  change codeProduct SixData.A (codeWord [true, false, false, true]) = w41
  rw [word_w40]
  exact product_w41

def w42 : CodeMatrix 6 :=
  !![2, 3, 2, 2, 2, 1;
    0, 3, 3, 3, 3, 1;
    1, 3, 2, 0, 3, 1;
    1, 2, 2, 3, 2, 0;
    2, 1, 3, 0, 2, 3;
    1, 3, 0, 0, 0, 2]

theorem product_w42 : codeProduct SixData.B w41 = w42 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w42 : codeWord [true, false, true, false, false, true] = w42 := by
  change codeProduct SixData.B (codeWord [false, true, false, false, true]) = w42
  rw [word_w41]
  exact product_w42

def w43 : CodeMatrix 6 :=
  !![3, 3, 1, 3, 1, 3;
    0, 1, 2, 3, 1, 1;
    1, 2, 1, 0, 3, 0;
    3, 2, 3, 0, 2, 1;
    1, 2, 3, 0, 2, 1;
    3, 2, 2, 3, 2, 0]

theorem product_w43 : codeProduct SixData.B w42 = w43 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w43 : codeWord [true, true, false, true, false, false, true] = w43 := by
  change codeProduct SixData.B (codeWord [true, false, true, false, false, true]) = w43
  rw [word_w42]
  exact product_w43

def w44 : CodeMatrix 6 :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem product_w44 : codeProduct SixData.A w1 = w44 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w44 : codeWord [false, false] = w44 := by
  change codeProduct SixData.A (codeWord [false]) = w44
  rw [word_w1]
  exact product_w44

def w45 : CodeMatrix 6 :=
  !![3, 3, 0, 0, 0, 0;
    1, 3, 0, 0, 0, 0;
    1, 1, 3, 3, 0, 0;
    2, 1, 1, 3, 0, 0;
    0, 3, 3, 3, 0, 2;
    3, 1, 3, 0, 3, 0]

theorem product_w45 : codeProduct SixData.A w44 = w45 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w45 : codeWord [false, false, false] = w45 := by
  change codeProduct SixData.A (codeWord [false, false]) = w45
  rw [word_w44]
  exact product_w45

def w46 : CodeMatrix 6 :=
  !![3, 1, 3, 3, 2, 1;
    1, 0, 2, 1, 1, 2;
    1, 3, 2, 3, 0, 2;
    3, 2, 0, 3, 3, 2;
    3, 3, 2, 1, 2, 3;
    2, 0, 3, 1, 1, 1]

theorem product_w46 : codeProduct SixData.B w45 = w46 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w46 : codeWord [true, false, false, false] = w46 := by
  change codeProduct SixData.B (codeWord [false, false, false]) = w46
  rw [word_w45]
  exact product_w46

def w47 : CodeMatrix 6 :=
  !![3, 0, 1, 1, 3, 2;
    1, 2, 3, 1, 1, 0;
    1, 2, 1, 2, 1, 2;
    1, 3, 1, 0, 3, 2;
    2, 1, 0, 2, 2, 3;
    0, 0, 1, 1, 2, 3]

theorem product_w47 : codeProduct SixData.B w46 = w47 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w47 : codeWord [true, true, false, false, false] = w47 := by
  change codeProduct SixData.B (codeWord [true, false, false, false]) = w47
  rw [word_w46]
  exact product_w47

def w48 : CodeMatrix 6 :=
  !![1, 1, 1, 0, 1, 1;
    0, 1, 3, 2, 0, 2;
    2, 1, 2, 1, 3, 2;
    2, 2, 3, 1, 3, 0;
    3, 2, 0, 0, 1, 1;
    1, 0, 3, 2, 1, 2]

theorem product_w48 : codeProduct SixData.A w47 = w48 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w48 : codeWord [false, true, true, false, false, false] = w48 := by
  change codeProduct SixData.A (codeWord [true, true, false, false, false]) = w48
  rw [word_w47]
  exact product_w48

def w49 : CodeMatrix 6 :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem product_w49 : codeProduct SixData.B w24 = w49 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w49 : codeWord [true, false, false, true, true] = w49 := by
  change codeProduct SixData.B (codeWord [false, false, true, true]) = w49
  rw [word_w24]
  exact product_w49

def w50 : CodeMatrix 6 :=
  !![2, 1, 3, 1, 3, 3;
    2, 1, 2, 1, 1, 2;
    2, 2, 3, 3, 1, 0;
    0, 0, 0, 0, 1, 1;
    3, 1, 3, 3, 2, 3;
    3, 1, 3, 2, 3, 2]

theorem product_w50 : codeProduct SixData.B w49 = w50 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w50 : codeWord [true, true, false, false, true, true] = w50 := by
  change codeProduct SixData.B (codeWord [true, false, false, true, true]) = w50
  rw [word_w49]
  exact product_w50

theorem linear_empty : codeLin [] [] = codeZero := rfl

def t7 : CodeMatrix 6 :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

theorem sum_t7 : codeAdd (codeScale 0 w50) codeZero = t7 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t7 : codeLin [[true, true, false, false, true, true]] [0] = t7 := by
  change codeAdd (codeScale 0 (codeWord [true, true, false, false, true, true])) (codeLin [] []) = t7
  rw [word_w50, linear_empty]
  exact sum_t7

def t6 : CodeMatrix 6 :=
  !![3, 3, 3, 0, 3, 3;
    0, 3, 2, 1, 0, 1;
    1, 3, 1, 3, 2, 1;
    1, 1, 2, 3, 2, 0;
    2, 1, 0, 0, 3, 3;
    3, 0, 2, 1, 3, 1]

theorem sum_t6 : codeAdd (codeScale 3 w48) t7 = t6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t6 : codeLin [[false, true, true, false, false, false], [true, true, false, false, true, true]] [3, 0] = t6 := by
  change codeAdd (codeScale 3 (codeWord [false, true, true, false, false, false])) (codeLin [[true, true, false, false, true, true]] [0]) = t6
  rw [word_w48, linear_t7]
  exact sum_t6

def t5 : CodeMatrix 6 :=
  !![0, 0, 3, 0, 3, 3;
    1, 0, 2, 1, 0, 1;
    0, 2, 2, 0, 2, 1;
    3, 0, 3, 0, 2, 0;
    2, 2, 3, 3, 3, 1;
    0, 1, 1, 1, 0, 1]

theorem sum_t5 : codeAdd (codeScale 1 w1) t6 = t5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t5 : codeLin [[false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [1, 3, 0] = t5 := by
  change codeAdd (codeScale 1 (codeWord [false])) (codeLin [[false, true, true, false, false, false], [true, true, false, false, true, true]] [3, 0]) = t5
  rw [word_w1, linear_t6]
  exact sum_t5

def t4 : CodeMatrix 6 :=
  !![1, 1, 1, 1, 1, 2;
    1, 2, 1, 0, 2, 3;
    2, 1, 0, 0, 3, 1;
    2, 3, 2, 0, 1, 2;
    0, 1, 2, 3, 0, 3;
    1, 2, 2, 0, 3, 1]

theorem sum_t4 : codeAdd (codeScale 2 w43) t5 = t4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t4 : codeLin [[true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [2, 1, 3, 0] = t4 := by
  change codeAdd (codeScale 2 (codeWord [true, true, false, true, false, false, true])) (codeLin [[false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [1, 3, 0]) = t4
  rw [word_w43, linear_t5]
  exact sum_t4

def t3 : CodeMatrix 6 :=
  !![1, 1, 1, 1, 1, 2;
    1, 2, 1, 0, 2, 3;
    2, 1, 0, 0, 3, 1;
    2, 3, 2, 0, 1, 2;
    0, 1, 2, 3, 0, 3;
    1, 2, 2, 0, 3, 1]

theorem sum_t3 : codeAdd (codeScale 0 w38) t4 = t3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t3 : codeLin [[false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [0, 2, 1, 3, 0] = t3 := by
  change codeAdd (codeScale 0 (codeWord [false, true, false, false, true, false, true])) (codeLin [[true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [2, 1, 3, 0]) = t3
  rw [word_w38, linear_t4]
  exact sum_t3

def t2 : CodeMatrix 6 :=
  !![3, 1, 2, 2, 3, 3;
    2, 3, 3, 3, 1, 3;
    1, 0, 3, 1, 0, 0;
    1, 1, 1, 0, 3, 3;
    1, 2, 2, 2, 1, 1;
    1, 2, 1, 3, 2, 3]

theorem sum_t2 : codeAdd (codeScale 3 w34) t3 = t2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t2 : codeLin [[true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [3, 0, 2, 1, 3, 0] = t2 := by
  change codeAdd (codeScale 3 (codeWord [true, false, false, false, false, true, false])) (codeLin [[false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [0, 2, 1, 3, 0]) = t2
  rw [word_w34, linear_t3]
  exact sum_t2

def t1 : CodeMatrix 6 :=
  !![3, 1, 2, 2, 3, 3;
    2, 3, 3, 3, 1, 3;
    1, 0, 3, 1, 0, 0;
    1, 1, 1, 0, 3, 3;
    1, 2, 2, 2, 1, 1;
    1, 2, 1, 3, 2, 3]

theorem sum_t1 : codeAdd (codeScale 0 w28) t2 = t1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t1 : codeLin [[false, false, false, false, false, false, true, true], [true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [0, 3, 0, 2, 1, 3, 0] = t1 := by
  change codeAdd (codeScale 0 (codeWord [false, false, false, false, false, false, true, true])) (codeLin [[true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [3, 0, 2, 1, 3, 0]) = t1
  rw [word_w28, linear_t2]
  exact sum_t1

def t0 : CodeMatrix 6 :=
  !![3, 0, 0, 0, 2, 2;
    1, 1, 3, 0, 0, 1;
    3, 0, 3, 0, 1, 2;
    2, 2, 0, 3, 3, 2;
    3, 3, 0, 3, 2, 0;
    3, 3, 3, 3, 0, 3]

theorem sum_t0 : codeAdd (codeScale 2 w23) t1 = t0 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem linear_t0 : codeLin [[true, false, true, true, false, true, true, true], [false, false, false, false, false, false, true, true], [true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [2, 0, 3, 0, 2, 1, 3, 0] = t0 := by
  change codeAdd (codeScale 2 (codeWord [true, false, true, true, false, true, true, true])) (codeLin [[false, false, false, false, false, false, true, true], [true, false, false, false, false, true, false], [false, true, false, false, true, false, true], [true, true, false, true, false, false, true], [false], [false, true, true, false, false, false], [true, true, false, false, true, true]] [0, 3, 0, 2, 1, 3, 0]) = t0
  rw [word_w23, linear_t1]
  exact sum_t0

theorem linear_combination : codeLin SixData.algebraWords SixData.algebraCoefficients = t0 :=
  linear_t0

theorem polynomial_empty : codePoly [] t0 = codeZero := rfl

def qp5 : CodeMatrix 6 :=
  !![0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

theorem product_qp5 : codeProduct t0 codeZero = qp5 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q5 : CodeMatrix 6 :=
  !![1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1]

theorem sum_q5 : codeAdd (codeScale 1 codeOne) qp5 = q5 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q5 : codePoly [1] t0 = q5 := by
  change codeAdd (codeScale 1 codeOne) (codeProduct t0 (codePoly [] t0)) = q5
  rw [polynomial_empty, product_qp5]
  exact sum_q5

def qp4 : CodeMatrix 6 :=
  !![3, 0, 0, 0, 2, 2;
    1, 1, 3, 0, 0, 1;
    3, 0, 3, 0, 1, 2;
    2, 2, 0, 3, 3, 2;
    3, 3, 0, 3, 2, 0;
    3, 3, 3, 3, 0, 3]

theorem product_qp4 : codeProduct t0 q5 = qp4 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q4 : CodeMatrix 6 :=
  !![2, 0, 0, 0, 2, 2;
    1, 0, 3, 0, 0, 1;
    3, 0, 2, 0, 1, 2;
    2, 2, 0, 2, 3, 2;
    3, 3, 0, 3, 3, 0;
    3, 3, 3, 3, 0, 2]

theorem sum_q4 : codeAdd (codeScale 1 codeOne) qp4 = q4 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q4 : codePoly [1, 1] t0 = q4 := by
  change codeAdd (codeScale 1 codeOne) (codeProduct t0 (codePoly [1] t0)) = q4
  rw [polynomial_q5, product_qp4]
  exact sum_q4

def qp3 : CodeMatrix 6 :=
  !![1, 0, 1, 0, 0, 2;
    2, 3, 1, 3, 1, 0;
    1, 2, 0, 2, 1, 3;
    3, 2, 0, 2, 3, 3;
    2, 0, 2, 0, 2, 3;
    3, 3, 1, 3, 0, 3]

theorem product_qp3 : codeProduct t0 q4 = qp3 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q3 : CodeMatrix 6 :=
  !![0, 0, 1, 0, 0, 2;
    2, 2, 1, 3, 1, 0;
    1, 2, 1, 2, 1, 3;
    3, 2, 0, 3, 3, 3;
    2, 0, 2, 0, 3, 3;
    3, 3, 1, 3, 0, 2]

theorem sum_q3 : codeAdd (codeScale 1 codeOne) qp3 = q3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q3 : codePoly [1, 1, 1] t0 = q3 := by
  change codeAdd (codeScale 1 codeOne) (codeProduct t0 (codePoly [1, 1] t0)) = q3
  rw [polynomial_q4, product_qp3]
  exact sum_q3

def qp2 : CodeMatrix 6 :=
  !![2, 1, 2, 1, 1, 3;
    2, 0, 2, 1, 2, 2;
    0, 0, 0, 0, 0, 3;
    1, 3, 3, 2, 2, 0;
    0, 0, 3, 0, 0, 2;
    2, 3, 0, 3, 2, 0]

theorem product_qp2 : codeProduct t0 q3 = qp2 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q2 : CodeMatrix 6 :=
  !![2, 1, 2, 1, 1, 3;
    2, 0, 2, 1, 2, 2;
    0, 0, 0, 0, 0, 3;
    1, 3, 3, 2, 2, 0;
    0, 0, 3, 0, 0, 2;
    2, 3, 0, 3, 2, 0]

theorem sum_q2 : codeAdd (codeScale 0 codeOne) qp2 = q2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q2 : codePoly [0, 1, 1, 1] t0 = q2 := by
  change codeAdd (codeScale 0 codeOne) (codeProduct t0 (codePoly [1, 1, 1] t0)) = q2
  rw [polynomial_q3, product_qp2]
  exact sum_q2

def qp1 : CodeMatrix 6 :=
  !![2, 2, 0, 2, 0, 1;
    2, 2, 0, 3, 1, 3;
    2, 2, 2, 2, 0, 2;
    0, 1, 0, 0, 3, 3;
    3, 1, 3, 1, 3, 0;
    2, 3, 2, 3, 2, 1]

theorem product_qp1 : codeProduct t0 q2 = qp1 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q1 : CodeMatrix 6 :=
  !![2, 2, 0, 2, 0, 1;
    2, 2, 0, 3, 1, 3;
    2, 2, 2, 2, 0, 2;
    0, 1, 0, 0, 3, 3;
    3, 1, 3, 1, 3, 0;
    2, 3, 2, 3, 2, 1]

theorem sum_q1 : codeAdd (codeScale 0 codeOne) qp1 = q1 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q1 : codePoly [0, 0, 1, 1, 1] t0 = q1 := by
  change codeAdd (codeScale 0 codeOne) (codeProduct t0 (codePoly [0, 1, 1, 1] t0)) = q1
  rw [polynomial_q2, product_qp1]
  exact sum_q1

def qp0 : CodeMatrix 6 :=
  !![3, 2, 2, 2, 2, 1;
    3, 2, 3, 3, 3, 2;
    0, 0, 1, 0, 0, 0;
    1, 1, 1, 0, 1, 3;
    1, 1, 1, 1, 0, 3;
    0, 0, 0, 0, 0, 1]

theorem product_qp0 : codeProduct t0 q1 = qp0 :=
  checkMatrix_sound _ _ (by decide +kernel)

def q0 : CodeMatrix 6 :=
  !![2, 2, 2, 2, 2, 1;
    3, 3, 3, 3, 3, 2;
    0, 0, 0, 0, 0, 0;
    1, 1, 1, 1, 1, 3;
    1, 1, 1, 1, 1, 3;
    0, 0, 0, 0, 0, 0]

theorem sum_q0 : codeAdd (codeScale 1 codeOne) qp0 = q0 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_q0 : codePoly [1, 0, 0, 1, 1, 1] t0 = q0 := by
  change codeAdd (codeScale 1 codeOne) (codeProduct t0 (codePoly [0, 0, 1, 1, 1] t0)) = q0
  rw [polynomial_q1, product_qp0]
  exact sum_q0

theorem factor_rankOne : q0 = codeOuter SixData.v SixData.lam :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem rankOne_identity :
    codePoly SixData.polynomial (codeLin SixData.algebraWords SixData.algebraCoefficients) =
      codeOuter SixData.v SixData.lam := by
  rw [linear_combination]
  exact polynomial_q0.trans factor_rankOne

theorem left_check_0 : codeMulVec codeOne SixData.v = (fun k => SixData.P k 0) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_0 : codeMulVec (codeWord (SixData.leftWords 0)) SixData.v = (fun k => SixData.P k 0) := by
  change codeMulVec (codeWord []) SixData.v = (fun k => SixData.P k 0)
  rw [word_empty]
  exact left_check_0

theorem left_check_1 : codeMulVec w1 SixData.v = (fun k => SixData.P k 1) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_1 : codeMulVec (codeWord (SixData.leftWords 1)) SixData.v = (fun k => SixData.P k 1) := by
  change codeMulVec (codeWord [false]) SixData.v = (fun k => SixData.P k 1)
  rw [word_w1]
  exact left_check_1

theorem left_check_2 : codeMulVec w2 SixData.v = (fun k => SixData.P k 2) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_2 : codeMulVec (codeWord (SixData.leftWords 2)) SixData.v = (fun k => SixData.P k 2) := by
  change codeMulVec (codeWord [true]) SixData.v = (fun k => SixData.P k 2)
  rw [word_w2]
  exact left_check_2

theorem left_check_3 : codeMulVec w3 SixData.v = (fun k => SixData.P k 3) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_3 : codeMulVec (codeWord (SixData.leftWords 3)) SixData.v = (fun k => SixData.P k 3) := by
  change codeMulVec (codeWord [false, true]) SixData.v = (fun k => SixData.P k 3)
  rw [word_w3]
  exact left_check_3

theorem left_check_4 : codeMulVec w7 SixData.v = (fun k => SixData.P k 4) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_4 : codeMulVec (codeWord (SixData.leftWords 4)) SixData.v = (fun k => SixData.P k 4) := by
  change codeMulVec (codeWord [true, true]) SixData.v = (fun k => SixData.P k 4)
  rw [word_w7]
  exact left_check_4

theorem left_check_5 : codeMulVec w8 SixData.v = (fun k => SixData.P k 5) :=
  checkVector_sound _ _ (by decide +kernel)

theorem left_orbit_5 : codeMulVec (codeWord (SixData.leftWords 5)) SixData.v = (fun k => SixData.P k 5) := by
  change codeMulVec (codeWord [false, true, true]) SixData.v = (fun k => SixData.P k 5)
  rw [word_w8]
  exact left_check_5

theorem left_orbit (i : Fin 6) : codeMulVec (codeWord (SixData.leftWords i)) SixData.v = fun k => SixData.P k i := by
  fin_cases i
  · exact left_orbit_0
  · exact left_orbit_1
  · exact left_orbit_2
  · exact left_orbit_3
  · exact left_orbit_4
  · exact left_orbit_5

theorem right_check_0 : codeVecMul SixData.lam codeOne = SixData.Q 0 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_0 : codeVecMul SixData.lam (codeWord (SixData.rightWords 0)) = SixData.Q 0 := by
  change codeVecMul SixData.lam (codeWord []) = SixData.Q 0
  rw [word_empty]
  exact right_check_0

theorem right_check_1 : codeVecMul SixData.lam w1 = SixData.Q 1 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_1 : codeVecMul SixData.lam (codeWord (SixData.rightWords 1)) = SixData.Q 1 := by
  change codeVecMul SixData.lam (codeWord [false]) = SixData.Q 1
  rw [word_w1]
  exact right_check_1

theorem right_check_2 : codeVecMul SixData.lam w2 = SixData.Q 2 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_2 : codeVecMul SixData.lam (codeWord (SixData.rightWords 2)) = SixData.Q 2 := by
  change codeVecMul SixData.lam (codeWord [true]) = SixData.Q 2
  rw [word_w2]
  exact right_check_2

theorem right_check_3 : codeVecMul SixData.lam w3 = SixData.Q 3 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_3 : codeVecMul SixData.lam (codeWord (SixData.rightWords 3)) = SixData.Q 3 := by
  change codeVecMul SixData.lam (codeWord [false, true]) = SixData.Q 3
  rw [word_w3]
  exact right_check_3

theorem right_check_4 : codeVecMul SixData.lam w29 = SixData.Q 4 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_4 : codeVecMul SixData.lam (codeWord (SixData.rightWords 4)) = SixData.Q 4 := by
  change codeVecMul SixData.lam (codeWord [true, false]) = SixData.Q 4
  rw [word_w29]
  exact right_check_4

theorem right_check_5 : codeVecMul SixData.lam w4 = SixData.Q 5 :=
  checkVector_sound _ _ (by decide +kernel)

theorem right_orbit_5 : codeVecMul SixData.lam (codeWord (SixData.rightWords 5)) = SixData.Q 5 := by
  change codeVecMul SixData.lam (codeWord [true, false, true]) = SixData.Q 5
  rw [word_w4]
  exact right_check_5

theorem right_orbit (i : Fin 6) : codeVecMul SixData.lam (codeWord (SixData.rightWords i)) = SixData.Q i := by
  fin_cases i
  · exact right_orbit_0
  · exact right_orbit_1
  · exact right_orbit_2
  · exact right_orbit_3
  · exact right_orbit_4
  · exact right_orbit_5

theorem inverse_P : codeProduct SixData.P SixData.Pi = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem inverse_Q : codeProduct SixData.Qi SixData.Q = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

def w51 : CodeMatrix 6 :=
  !![3, 0, 1, 1, 3, 2;
    1, 2, 3, 1, 1, 0;
    1, 2, 1, 2, 1, 2;
    1, 3, 1, 0, 3, 2;
    2, 1, 0, 2, 2, 3;
    0, 0, 1, 1, 2, 3]

theorem product_w51 : codeProduct SixData.B w29 = w51 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w51 : codeWord [true, true, false] = w51 := by
  change codeProduct SixData.B (codeWord [true, false]) = w51
  rw [word_w29]
  exact product_w51

def w52 : CodeMatrix 6 :=
  !![1, 1, 1, 0, 1, 1;
    0, 1, 3, 2, 0, 2;
    2, 1, 2, 1, 3, 2;
    2, 2, 3, 1, 3, 0;
    3, 2, 0, 0, 1, 1;
    1, 0, 3, 2, 1, 2]

theorem product_w52 : codeProduct SixData.A w51 = w52 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w52 : codeWord [false, true, true, false] = w52 := by
  change codeProduct SixData.A (codeWord [true, true, false]) = w52
  rw [word_w51]
  exact product_w52

def w53 : CodeMatrix 6 :=
  !![0, 3, 1, 1, 3, 3;
    2, 1, 0, 2, 3, 1;
    1, 0, 0, 3, 3, 1;
    2, 2, 3, 2, 0, 3;
    1, 3, 1, 3, 2, 3;
    1, 3, 1, 0, 1, 0]

theorem product_w53 : codeProduct SixData.B w52 = w53 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w53 : codeWord [true, false, true, true, false] = w53 := by
  change codeProduct SixData.B (codeWord [false, true, true, false]) = w53
  rw [word_w52]
  exact product_w53

def w54 : CodeMatrix 6 :=
  !![3, 2, 1, 2, 2, 2;
    1, 0, 2, 0, 3, 2;
    0, 1, 1, 1, 0, 1;
    0, 0, 0, 3, 3, 3;
    1, 1, 0, 3, 3, 3;
    3, 3, 3, 2, 0, 3]

theorem product_w54 : codeProduct SixData.B w53 = w54 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w54 : codeWord [true, true, false, true, true, false] = w54 := by
  change codeProduct SixData.B (codeWord [true, false, true, true, false]) = w54
  rw [word_w53]
  exact product_w54

def w55 : CodeMatrix 6 :=
  !![1, 1, 2, 1, 3, 0;
    0, 2, 0, 2, 0, 3;
    2, 1, 0, 3, 3, 1;
    0, 2, 1, 0, 2, 2;
    2, 2, 3, 2, 0, 1;
    0, 1, 2, 0, 0, 2]

theorem product_w55 : codeProduct SixData.A w54 = w55 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w55 : codeWord [false, true, true, false, true, true, false] = w55 := by
  change codeProduct SixData.A (codeWord [true, true, false, true, true, false]) = w55
  rw [word_w54]
  exact product_w55

def w56 : CodeMatrix 6 :=
  !![2, 3, 1, 3, 1, 0;
    3, 0, 2, 3, 2, 1;
    1, 1, 3, 1, 2, 2;
    2, 3, 1, 2, 0, 3;
    1, 3, 2, 0, 1, 2;
    3, 2, 2, 2, 3, 3]

theorem product_w56 : codeProduct SixData.B w55 = w56 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w56 : codeWord [true, false, true, true, false, true, true, false] = w56 := by
  change codeProduct SixData.B (codeWord [false, true, true, false, true, true, false]) = w56
  rw [word_w55]
  exact product_w56

def w57 : CodeMatrix 6 :=
  !![3, 2, 2, 0, 2, 3;
    0, 3, 0, 1, 0, 3;
    3, 2, 2, 2, 2, 2;
    0, 2, 0, 2, 2, 1;
    1, 2, 3, 3, 1, 1;
    2, 3, 2, 2, 3, 1]

theorem product_w57 : codeProduct SixData.A w56 = w57 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w57 : codeWord [false, true, false, true, true, false, true, true, false] = w57 := by
  change codeProduct SixData.A (codeWord [true, false, true, true, false, true, true, false]) = w57
  rw [word_w56]
  exact product_w57

def w58 : CodeMatrix 6 :=
  !![1, 0, 1, 1, 1, 2;
    2, 2, 0, 0, 2, 3;
    2, 0, 1, 1, 2, 3;
    3, 1, 1, 1, 2, 0;
    3, 3, 0, 1, 1, 2;
    0, 0, 1, 2, 1, 3]

theorem product_w58 : codeProduct SixData.B w57 = w58 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w58 : codeWord [true, false, true, false, true, true, false, true, true, false] = w58 := by
  change codeProduct SixData.B (codeWord [false, true, false, true, true, false, true, true, false]) = w58
  rw [word_w57]
  exact product_w58

def w59 : CodeMatrix 6 :=
  !![2, 1, 3, 3, 2, 3;
    0, 1, 1, 1, 0, 0;
    0, 1, 1, 1, 3, 3;
    0, 1, 0, 0, 3, 3;
    2, 2, 2, 3, 3, 1;
    2, 0, 0, 3, 3, 1]

theorem product_w59 : codeProduct SixData.A w58 = w59 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w59 : codeWord [false, true, false, true, false, true, true, false, true, true, false] = w59 := by
  change codeProduct SixData.A (codeWord [true, false, true, false, true, true, false, true, true, false]) = w59
  rw [word_w58]
  exact product_w59

def w60 : CodeMatrix 6 :=
  !![3, 0, 2, 3, 2, 0;
    2, 2, 0, 0, 3, 0;
    1, 2, 2, 3, 0, 0;
    0, 2, 2, 0, 0, 0;
    3, 1, 3, 3, 2, 3;
    3, 2, 1, 3, 1, 0]

theorem product_w60 : codeProduct SixData.B w59 = w60 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w60 : codeWord [true, false, true, false, true, false, true, true, false, true, true, false] = w60 := by
  change codeProduct SixData.B (codeWord [false, true, false, true, false, true, true, false, true, true, false]) = w60
  rw [word_w59]
  exact product_w60

def w61 : CodeMatrix 6 :=
  !![0, 3, 1, 3, 2, 2;
    3, 1, 3, 2, 0, 3;
    2, 2, 0, 0, 0, 3;
    0, 3, 2, 0, 3, 3;
    0, 1, 3, 3, 2, 1;
    0, 0, 3, 3, 1, 2]

theorem product_w61 : codeProduct SixData.B w60 = w61 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w61 : codeWord [true, true, false, true, false, true, false, true, true, false, true, true, false] = w61 := by
  change codeProduct SixData.B (codeWord [true, false, true, false, true, false, true, true, false, true, true, false]) = w61
  rw [word_w60]
  exact product_w61

def w62 : CodeMatrix 6 :=
  !![2, 1, 1, 3, 1, 3;
    2, 0, 3, 2, 2, 0;
    2, 1, 3, 1, 0, 1;
    1, 0, 0, 3, 1, 1;
    3, 0, 2, 0, 0, 1;
    2, 1, 2, 2, 0, 3]

theorem product_w62 : codeProduct SixData.A w61 = w62 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w62 : codeWord [false, true, true, false, true, false, true, false, true, true, false, true, true, false] = w62 := by
  change codeProduct SixData.A (codeWord [true, true, false, true, false, true, false, true, true, false, true, true, false]) = w62
  rw [word_w61]
  exact product_w62

def w63 : CodeMatrix 6 :=
  !![2, 2, 3, 2, 1, 2;
    3, 2, 1, 1, 1, 2;
    1, 1, 3, 3, 2, 0;
    1, 1, 0, 2, 0, 2;
    1, 3, 0, 0, 2, 2;
    1, 2, 0, 1, 3, 1]

theorem product_w63 : codeProduct SixData.B w62 = w63 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem word_w63 : codeWord [true, false, true, true, false, true, false, true, false, true, true, false, true, true, false] = w63 := by
  change codeProduct SixData.B (codeWord [false, true, true, false, true, false, true, false, true, true, false, true, true, false]) = w63
  rw [word_w62]
  exact product_w63

theorem trace_check : codeTrace w63 = SixData.traceCode := by decide +kernel

theorem trace_identity : codeTrace (codeWord SixData.traceWord) = SixData.traceCode := by
  change codeTrace (codeWord [true, false, true, true, false, true, false, true, false, true, true, false, true, true, false]) = SixData.traceCode
  rw [word_w63]
  exact trace_check

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.SixCertificate
