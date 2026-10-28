module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Evaluation

/-!
# TraceWords: checked positive words

Successive suffix products certify the supplied fifteen-letter trace word.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

namespace TraceWords

omit [CharP F 2] in
theorem Wb_eval (t : F) (_ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true] =
      evalMatrix t FourteenData.B := by
  exact word_singleton _ _ _

def Wab : CodeMatrix 14 :=
  !![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 3, 1, 2, 1, 2, 1, 0, 3, 1, 3, 1, 0, 2;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1]

theorem Wab_product : codeProduct FourteenData.A FourteenData.B = Wab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true] =
      evalMatrix t Wab := by
  rw [word_cons, Wb_eval t ht]
  exact product_eq t ht _ _ _ Wab_product

def Wbab : CodeMatrix 14 :=
  !![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 3, 1, 2, 1, 2, 1, 0, 3, 1, 3, 1, 0, 2;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2]

theorem Wbab_product : codeProduct FourteenData.B Wab = Wbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true] =
      evalMatrix t Wbab := by
  rw [word_cons, Wab_eval t ht]
  exact product_eq t ht _ _ _ Wbab_product

def Wbbab : CodeMatrix 14 :=
  !![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

theorem Wbbab_product : codeProduct FourteenData.B Wbab = Wbbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, false, true] =
      evalMatrix t Wbbab := by
  rw [word_cons, Wbab_eval t ht]
  exact product_eq t ht _ _ _ Wbbab_product

def Wabbab : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 0, 0, 0, 1, 2, 0, 2, 3, 3, 0, 2, 2, 2;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    3, 1, 1, 2, 1, 3, 0, 0, 3, 1, 2, 3, 0, 1]

theorem Wabbab_product : codeProduct FourteenData.A Wbbab = Wabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true] =
      evalMatrix t Wabbab := by
  rw [word_cons, Wbbab_eval t ht]
  exact product_eq t ht _ _ _ Wabbab_product

def Wbabbab : CodeMatrix 14 :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 0, 0, 0, 1, 2, 0, 2, 3, 3, 0, 2, 2, 2;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    3, 1, 1, 2, 1, 3, 0, 0, 3, 1, 2, 3, 0, 1;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1]

theorem Wbabbab_product : codeProduct FourteenData.B Wabbab = Wbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true, false, true] =
      evalMatrix t Wbabbab := by
  rw [word_cons, Wabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbabbab_product

def Wbbabbab : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

theorem Wbbabbab_product : codeProduct FourteenData.B Wbabbab = Wbbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, false, true, true, false, true] =
      evalMatrix t Wbbabbab := by
  rw [word_cons, Wbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbbabbab_product

def Wabbabbab : CodeMatrix 14 :=
  !![0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3]

theorem Wabbabbab_product : codeProduct FourteenData.A Wbbabbab = Wabbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true, true, false, true] =
      evalMatrix t Wabbabbab := by
  rw [word_cons, Wbbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wabbabbab_product

def Wbabbabbab : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2]

theorem Wbabbabbab_product : codeProduct FourteenData.B Wabbabbab = Wbabbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wbabbabbab := by
  rw [word_cons, Wabbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbabbabbab_product

def Wababbabbab : CodeMatrix 14 :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    1, 2, 3, 3, 1, 3, 1, 1, 2, 0, 0, 0, 1, 1;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 0, 3, 3, 0, 3, 0, 2, 1, 1, 2, 2, 3, 3]

theorem Wababbabbab_product : codeProduct FourteenData.A Wbabbabbab = Wababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wababbabbab := by
  rw [word_cons, Wbabbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wababbabbab_product

def Wbababbabbab : CodeMatrix 14 :=
  !![0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    0, 1, 0, 1, 0, 2, 0, 0, 2, 0, 3, 2, 1, 2;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 3, 3, 1, 2;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    1, 2, 3, 3, 1, 3, 1, 1, 2, 0, 0, 0, 1, 1;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 2, 0, 2, 0, 3, 0, 2, 2, 3, 0, 1, 3, 3;
    3, 0, 3, 3, 0, 3, 0, 2, 1, 1, 2, 2, 3, 3;
    3, 1, 3, 2, 0, 3, 2, 3, 1, 3, 0, 0, 3, 2]

theorem Wbababbabbab_product : codeProduct FourteenData.B Wababbabbab = Wbababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wbababbabbab := by
  rw [word_cons, Wababbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbababbabbab_product

def Wbbababbabbab : CodeMatrix 14 :=
  !![0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 3, 3, 1, 2;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    0, 2, 0, 2, 0, 3, 0, 2, 2, 3, 0, 1, 3, 3;
    1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 3, 2, 0, 3, 2, 3, 1, 3, 0, 0, 3, 2;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem Wbbababbabbab_product : codeProduct FourteenData.B Wbababbabbab = Wbbababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wbbababbabbab := by
  rw [word_cons, Wbababbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbbababbabbab_product

def Wabbababbabbab : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 3, 3, 1, 2;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 2, 0, 2, 0, 3, 0, 2, 2, 3, 0, 1, 3, 3;
    1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 0;
    0, 1, 1, 0, 0, 2, 0, 2, 3, 3, 0, 3, 2, 3;
    0, 1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0;
    3, 1, 3, 2, 0, 3, 2, 3, 1, 3, 0, 0, 3, 2;
    3, 2, 2, 1, 0, 1, 2, 1, 3, 1, 1, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    1, 2, 2, 0, 3, 1, 0, 3, 2, 0, 2, 3, 1, 1]

theorem Wabbababbabbab_product : codeProduct FourteenData.A Wbbababbabbab = Wabbababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wabbababbabbab := by
  rw [word_cons, Wbbababbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wabbababbabbab_product

def Wbabbababbabbab : CodeMatrix 14 :=
  !![1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    1, 1, 0, 1, 0, 3, 1, 2, 2, 2, 1, 1, 1, 0;
    1, 0, 0, 0, 0, 1, 1, 2, 0, 2, 2, 3, 0, 2;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    0, 2, 0, 2, 0, 3, 0, 2, 2, 3, 0, 1, 3, 3;
    1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    3, 1, 3, 2, 0, 3, 2, 3, 1, 3, 0, 0, 3, 2;
    3, 2, 2, 1, 0, 1, 2, 1, 3, 1, 1, 0, 0, 1;
    0, 1, 1, 1, 0, 0, 0, 2, 1, 3, 2, 0, 3, 1;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 2, 1, 3, 1, 1, 1, 2, 0, 3, 2, 2, 2, 1;
    1, 2, 2, 0, 3, 1, 0, 3, 2, 0, 2, 3, 1, 1;
    0, 3, 0, 0, 0, 3, 3, 2, 2, 1, 0, 2, 0, 1]

theorem Wbabbababbabbab_product : codeProduct FourteenData.B Wabbababbabbab = Wbabbababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabbababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true, false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wbabbababbabbab := by
  rw [word_cons, Wabbababbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wbabbababbabbab_product

def Wababbababbabbab : CodeMatrix 14 :=
  !![1, 1, 0, 1, 0, 3, 1, 2, 2, 2, 1, 1, 1, 0;
    1, 1, 0, 0, 0, 1, 1, 2, 0, 2, 2, 2, 0, 2;
    1, 3, 3, 2, 0, 3, 1, 2, 3, 3, 3, 2, 1, 3;
    1, 0, 0, 0, 0, 1, 1, 2, 0, 2, 2, 3, 0, 2;
    1, 2, 2, 2, 1, 3, 1, 3, 3, 3, 3, 1, 2, 0;
    0, 2, 0, 2, 0, 3, 0, 2, 2, 3, 0, 1, 3, 3;
    3, 2, 2, 1, 0, 1, 2, 1, 3, 1, 1, 0, 0, 1;
    0, 1, 1, 1, 0, 0, 0, 2, 1, 3, 2, 0, 3, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    3, 1, 3, 2, 0, 3, 2, 3, 1, 3, 0, 0, 3, 2;
    1, 2, 2, 0, 3, 1, 0, 3, 2, 0, 2, 3, 1, 1;
    3, 2, 0, 3, 2, 0, 2, 1, 1, 3, 0, 3, 0, 3;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    3, 3, 3, 2, 3, 2, 0, 1, 2, 3, 0, 2, 1, 0]

theorem Wababbababbabbab_product : codeProduct FourteenData.A Wbabbababbabbab = Wababbababbabbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wababbababbabbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, true, false, true, false, true, true, false, true, true, false, true] =
      evalMatrix t Wababbababbabbab := by
  rw [word_cons, Wbabbababbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wababbababbabbab_product

end TraceWords

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
