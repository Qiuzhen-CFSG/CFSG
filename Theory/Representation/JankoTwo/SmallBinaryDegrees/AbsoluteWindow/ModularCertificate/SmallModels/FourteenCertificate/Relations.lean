module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.RelationWords

/-!
# The five ATLAS matrix relations

Short addition chains check the powers of the three literal relation
words. No presentation injectivity or group identification is used.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

open RelationWords

theorem A_square_code : codeProduct FourteenData.A FourteenData.A = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

def B2 : CodeMatrix 14 :=
  !![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

theorem B_square_code : codeProduct FourteenData.B FourteenData.B = B2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem B_cube_code : codeProduct B2 FourteenData.B = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

def seven2 : CodeMatrix 14 :=
  !![0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 3, 1, 2, 1, 2, 1, 0, 3, 1, 3, 1, 0, 2;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1;
    0, 0, 3, 3, 3, 1, 1, 3, 0, 0, 3, 3, 2, 3;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 3, 2, 1, 2, 0, 1, 3, 2, 1, 1, 1, 1, 1]

theorem seven2_code : codeProduct Wab Wab = seven2 :=
  checkMatrix_sound _ _ (by decide +kernel)

def seven3 : CodeMatrix 14 :=
  !![0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 3, 1, 2, 1, 2, 1, 0, 3, 1, 3, 1, 0, 2;
    0, 0, 3, 3, 3, 1, 1, 3, 0, 0, 3, 3, 2, 3;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1;
    0, 3, 2, 1, 2, 0, 1, 3, 2, 1, 1, 1, 1, 1;
    0, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 3, 3, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 2, 1, 2, 1, 1, 0, 3, 2, 2, 1, 2, 1, 2]

theorem seven3_code : codeProduct seven2 Wab = seven3 :=
  checkMatrix_sound _ _ (by decide +kernel)

def seven6 : CodeMatrix 14 :=
  !![0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 1, 1, 3, 1, 3, 2, 1, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 3, 3, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]

theorem seven6_code : codeProduct seven3 seven3 = seven6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem seven7_code : codeProduct seven6 Wab = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem seven2_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 2 = evalMatrix t seven2 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 1 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 1 := pow_add _ 1 1
    _ = evalMatrix t Wab * evalMatrix t Wab := by
      rw [pow_one, Wab_eval t ht]
    _ = evalMatrix t seven2 := product_eq t ht _ _ _ seven2_code

theorem seven3_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 3 = evalMatrix t seven3 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 2 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 1 := pow_add _ 2 1
    _ = evalMatrix t seven2 * evalMatrix t Wab := by
      rw [pow_one, seven2_eval t ht, Wab_eval t ht]
    _ = evalMatrix t seven3 := product_eq t ht _ _ _ seven3_code

theorem seven6_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 6 = evalMatrix t seven6 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 3 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 3 := pow_add _ 3 3
    _ = evalMatrix t seven3 * evalMatrix t seven3 := by
      rw [seven3_eval t ht]
    _ = evalMatrix t seven6 := product_eq t ht _ _ _ seven6_code

theorem seven7_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 7 = evalMatrix t codeOne := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 6 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true]) ^ 1 := pow_add _ 6 1
    _ = evalMatrix t seven6 * evalMatrix t Wab := by
      rw [pow_one, seven6_eval t ht, Wab_eval t ht]
    _ = evalMatrix t codeOne := product_eq t ht _ _ _ seven7_code

def twelve2 : CodeMatrix 14 :=
  !![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 1, 2, 0, 2, 3, 3, 0, 2, 2, 2;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    3, 1, 1, 2, 1, 3, 0, 0, 3, 1, 2, 3, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 1, 1, 0, 0, 0, 2, 1, 3, 2, 1, 3, 0;
    3, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    3, 2, 1, 0, 1, 3, 0, 3, 1, 0, 0, 1, 3, 0;
    3, 1, 0, 2, 0, 1, 1, 2, 3, 1, 2, 0, 3, 3;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2]

theorem twelve2_code : codeProduct Wabbab Wabbab = twelve2 :=
  checkMatrix_sound _ _ (by decide +kernel)

def twelve3 : CodeMatrix 14 :=
  !![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    3, 0, 0, 2, 1, 1, 0, 2, 0, 2, 2, 0, 2, 2;
    3, 1, 0, 2, 0, 1, 1, 2, 3, 1, 2, 0, 3, 3;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 1, 1, 0, 3, 1, 1, 2, 2, 3, 1, 2, 3, 2;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 2, 2, 2;
    0, 2, 0, 2, 0, 2, 1, 1, 2, 1, 2, 0, 0, 2;
    2, 2, 0, 0, 3, 0, 0, 2, 0, 0, 1, 1, 2, 1;
    3, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3;
    0, 1, 1, 1, 0, 0, 0, 2, 1, 3, 2, 1, 3, 0;
    3, 0, 1, 2, 3, 3, 3, 0, 2, 0, 2, 0, 2, 2;
    3, 0, 1, 3, 2, 2, 3, 1, 3, 1, 2, 0, 2, 3;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 3;
    0, 0, 2, 2, 1, 3, 1, 3, 0, 1, 1, 3, 2, 3]

theorem twelve3_code : codeProduct twelve2 Wabbab = twelve3 :=
  checkMatrix_sound _ _ (by decide +kernel)

def twelve6 : CodeMatrix 14 :=
  !![3, 0, 2, 1, 1, 0, 2, 0, 2, 0, 2, 1, 2, 3;
    2, 1, 2, 1, 2, 3, 0, 0, 0, 0, 0, 1, 0, 3;
    3, 1, 1, 3, 1, 0, 0, 2, 0, 2, 2, 1, 2, 3;
    3, 1, 0, 2, 2, 3, 2, 2, 2, 2, 0, 1, 0, 3;
    0, 1, 3, 3, 0, 3, 0, 0, 1, 2, 3, 2, 0, 3;
    0, 1, 3, 3, 1, 2, 0, 0, 1, 2, 3, 2, 0, 3;
    3, 3, 2, 3, 2, 0, 2, 3, 0, 3, 3, 1, 0, 1;
    2, 3, 3, 3, 3, 0, 0, 1, 1, 3, 2, 0, 0, 1;
    3, 3, 1, 0, 3, 1, 0, 1, 2, 1, 2, 1, 1, 1;
    2, 3, 0, 0, 3, 0, 0, 2, 1, 0, 0, 0, 2, 1;
    3, 2, 2, 3, 2, 2, 0, 1, 2, 3, 0, 3, 1, 2;
    2, 1, 1, 2, 3, 0, 0, 0, 1, 2, 3, 2, 0, 0;
    3, 2, 1, 0, 3, 3, 3, 3, 1, 1, 0, 3, 1, 2;
    1, 1, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 0, 1]

theorem twelve6_code : codeProduct twelve3 twelve3 = twelve6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem twelve12_code : codeProduct twelve6 twelve6 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem twelve2_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 2 = evalMatrix t twelve2 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 1 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 1 := pow_add _ 1 1
    _ = evalMatrix t Wabbab * evalMatrix t Wabbab := by
      rw [pow_one, Wabbab_eval t ht]
    _ = evalMatrix t twelve2 := product_eq t ht _ _ _ twelve2_code

theorem twelve3_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 3 = evalMatrix t twelve3 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 2 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 1 := pow_add _ 2 1
    _ = evalMatrix t twelve2 * evalMatrix t Wabbab := by
      rw [pow_one, twelve2_eval t ht, Wabbab_eval t ht]
    _ = evalMatrix t twelve3 := product_eq t ht _ _ _ twelve3_code

theorem twelve6_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 6 = evalMatrix t twelve6 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 3 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 3 := pow_add _ 3 3
    _ = evalMatrix t twelve3 * evalMatrix t twelve3 := by
      rw [twelve3_eval t ht]
    _ = evalMatrix t twelve6 := product_eq t ht _ _ _ twelve6_code

theorem twelve12_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 12 = evalMatrix t codeOne := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 6 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true]) ^ 6 := pow_add _ 6 6
    _ = evalMatrix t twelve6 * evalMatrix t twelve6 := by
      rw [twelve6_eval t ht]
    _ = evalMatrix t codeOne := product_eq t ht _ _ _ twelve12_code

def six2 : CodeMatrix 14 :=
  !![2, 0, 2, 2, 0, 0, 3, 1, 3, 1, 3, 2, 3, 1;
    0, 3, 1, 0, 3, 2, 0, 2, 1, 1, 1, 2, 3, 3;
    1, 3, 2, 0, 1, 1, 1, 0, 0, 3, 1, 0, 1, 2;
    2, 2, 2, 2, 0, 3, 1, 3, 0, 0, 3, 3, 0, 2;
    2, 3, 1, 2, 0, 1, 2, 1, 3, 2, 2, 2, 2, 3;
    0, 1, 2, 2, 0, 3, 2, 3, 2, 3, 3, 0, 1, 1;
    3, 0, 1, 3, 0, 3, 3, 2, 2, 0, 0, 2, 1, 3;
    2, 2, 0, 3, 1, 0, 2, 1, 2, 3, 2, 1, 1, 1;
    2, 1, 2, 1, 2, 1, 2, 2, 0, 0, 1, 0, 0, 1;
    0, 2, 1, 1, 2, 3, 1, 0, 2, 3, 2, 3, 3, 0;
    0, 3, 3, 0, 1, 2, 1, 3, 2, 3, 2, 0, 2, 3;
    2, 1, 3, 1, 2, 0, 3, 2, 1, 1, 0, 2, 3, 3;
    0, 3, 2, 1, 1, 3, 0, 2, 3, 0, 2, 1, 0, 2;
    2, 1, 1, 0, 0, 0, 0, 1, 3, 3, 3, 1, 2, 2]

theorem six2_code : codeProduct Wabababbababb Wabababbababb = six2 :=
  checkMatrix_sound _ _ (by decide +kernel)

def six3 : CodeMatrix 14 :=
  !![3, 3, 2, 3, 2, 0, 2, 2, 2, 1, 2, 3, 3, 3;
    1, 1, 1, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 3;
    2, 1, 0, 3, 3, 3, 2, 1, 1, 3, 0, 0, 2, 2;
    3, 3, 0, 2, 2, 0, 2, 2, 1, 0, 2, 3, 2, 0;
    1, 1, 2, 3, 1, 0, 1, 2, 1, 2, 0, 2, 1, 2;
    2, 0, 3, 2, 0, 1, 3, 0, 0, 1, 3, 0, 2, 0;
    0, 0, 2, 3, 3, 1, 2, 3, 2, 0, 0, 2, 1, 1;
    3, 0, 1, 3, 0, 3, 3, 2, 2, 0, 0, 2, 1, 3;
    1, 1, 3, 1, 2, 2, 0, 3, 1, 3, 0, 1, 1, 3;
    1, 0, 1, 0, 1, 0, 2, 1, 1, 1, 3, 3, 2, 3;
    1, 2, 0, 2, 3, 0, 2, 1, 1, 3, 3, 2, 3, 1;
    2, 3, 1, 3, 3, 3, 2, 2, 1, 0, 2, 2, 2, 3;
    3, 1, 0, 3, 2, 3, 0, 2, 3, 1, 1, 2, 1, 2;
    0, 1, 1, 3, 2, 1, 1, 2, 3, 1, 0, 2, 2, 0]

theorem six3_code : codeProduct six2 Wabababbababb = six3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem six6_code : codeProduct six3 six3 = codeOne :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem six2_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 2 = evalMatrix t six2 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 1 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 1 := pow_add _ 1 1
    _ = evalMatrix t Wabababbababb * evalMatrix t Wabababbababb := by
      rw [pow_one, Wabababbababb_eval t ht]
    _ = evalMatrix t six2 := product_eq t ht _ _ _ six2_code

theorem six3_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 3 = evalMatrix t six3 := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 2 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 1 := pow_add _ 2 1
    _ = evalMatrix t six2 * evalMatrix t Wabababbababb := by
      rw [pow_one, six2_eval t ht, Wabababbababb_eval t ht]
    _ = evalMatrix t six3 := product_eq t ht _ _ _ six3_code

theorem six6_eval (t : F) (ht : t ^ 2 = t + 1) :
    (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 6 = evalMatrix t codeOne := by
  calc
    _ = (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 3 *
        (wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true]) ^ 3 := pow_add _ 3 3
    _ = evalMatrix t six3 * evalMatrix t six3 := by
      rw [six3_eval t ht]
    _ = evalMatrix t codeOne := product_eq t ht _ _ _ six6_code

theorem relations (t : F) (ht : t ^ 2 = t + 1) :
    MatrixRelations (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) := by
  have ha := (product_eq t ht _ _ _ A_square_code).trans (eval_one t)
  have hb2 := product_eq t ht _ _ _ B_square_code
  have hb3 := (product_eq t ht _ _ _ B_cube_code).trans (eval_one t)
  refine ⟨by simpa only [pow_two] using ha, ?_, ?_, ?_, ?_⟩
  · rw [pow_succ, pow_two, hb2]
    exact hb3
  · have h := (seven7_eval t ht).trans (eval_one t)
    simpa only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, if_true, mul_one, pow_two, Matrix.mul_assoc] using h
  · have h := (twelve12_eval t ht).trans (eval_one t)
    simpa only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, if_true, mul_one, pow_two, Matrix.mul_assoc] using h
  · have h := (six6_eval t ht).trans (eval_one t)
    simpa only [wordValue, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Bool.false_eq_true, if_false, if_true, mul_one, pow_two, Matrix.mul_assoc] using h

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
