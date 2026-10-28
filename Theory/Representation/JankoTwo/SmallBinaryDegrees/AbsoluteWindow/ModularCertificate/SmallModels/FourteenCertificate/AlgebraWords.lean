module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Evaluation

/-!
# AlgebraWords: checked positive words

Only the four words with nonzero coefficients in the supplied algebra
combination are needed. Every suffix product has an explicit literal result.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

namespace AlgebraWords

omit [CharP F 2] in
theorem Wa_eval (t : F) (_ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false] =
      evalMatrix t FourteenData.A := by
  exact word_singleton _ _ _

omit [CharP F 2] in
theorem Wb_eval (t : F) (_ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true] =
      evalMatrix t FourteenData.B := by
  exact word_singleton _ _ _

def Waa : CodeMatrix 14 :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem Waa_product : codeProduct FourteenData.A FourteenData.A = Waa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Waa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, false] =
      evalMatrix t Waa := by
  rw [word_cons, Wa_eval t ht]
  exact product_eq t ht _ _ _ Waa_product

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

def Wbb : CodeMatrix 14 :=
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

theorem Wbb_product : codeProduct FourteenData.B FourteenData.B = Wbb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true] =
      evalMatrix t Wbb := by
  rw [word_cons, Wb_eval t ht]
  exact product_eq t ht _ _ _ Wbb_product

def Wabb : CodeMatrix 14 :=
  !![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0]

theorem Wabb_product : codeProduct FourteenData.A Wbb = Wabb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true] =
      evalMatrix t Wabb := by
  rw [word_cons, Wbb_eval t ht]
  exact product_eq t ht _ _ _ Wabb_product

def Wbaa : CodeMatrix 14 :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1]

theorem Wbaa_product : codeProduct FourteenData.B Waa = Wbaa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbaa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, false] =
      evalMatrix t Wbaa := by
  rw [word_cons, Waa_eval t ht]
  exact product_eq t ht _ _ _ Wbaa_product

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

def Wbbb : CodeMatrix 14 :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem Wbbb_product : codeProduct FourteenData.B Wbb = Wbbb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, true] =
      evalMatrix t Wbbb := by
  rw [word_cons, Wbb_eval t ht]
  exact product_eq t ht _ _ _ Wbbb_product

def Wabaa : CodeMatrix 14 :=
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

theorem Wabaa_product : codeProduct FourteenData.A Wbaa = Wabaa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabaa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, false] =
      evalMatrix t Wabaa := by
  rw [word_cons, Wbaa_eval t ht]
  exact product_eq t ht _ _ _ Wabaa_product

def Wabbb : CodeMatrix 14 :=
  !![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 1, 1, 0, 0, 1, 3, 1, 3, 2, 1, 2, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 0, 0, 0, 1]

theorem Wabbb_product : codeProduct FourteenData.A Wbbb = Wabbb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, true] =
      evalMatrix t Wabbb := by
  rw [word_cons, Wbbb_eval t ht]
  exact product_eq t ht _ _ _ Wabbb_product

def Wbabb : CodeMatrix 14 :=
  !![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    0, 0, 2, 2, 3, 1, 0, 1, 1, 2, 3, 3, 2, 3]

theorem Wbabb_product : codeProduct FourteenData.B Wabb = Wbabb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true] =
      evalMatrix t Wbabb := by
  rw [word_cons, Wabb_eval t ht]
  exact product_eq t ht _ _ _ Wbabb_product

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

def Waabaa : CodeMatrix 14 :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1]

theorem Waabaa_product : codeProduct FourteenData.A Wabaa = Waabaa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Waabaa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, false, true, false, false] =
      evalMatrix t Waabaa := by
  rw [word_cons, Wabaa_eval t ht]
  exact product_eq t ht _ _ _ Waabaa_product

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

def Wbabbb : CodeMatrix 14 :=
  !![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 1, 1, 1, 0, 0, 1, 3, 1, 3, 2, 1, 2, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0;
    1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 0, 0, 0, 1;
    0, 0, 1, 1, 1, 2, 1, 0, 0, 1, 0, 3, 3, 1]

theorem Wbabbb_product : codeProduct FourteenData.B Wabbb = Wbabbb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabbb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true, true] =
      evalMatrix t Wbabbb := by
  rw [word_cons, Wabbb_eval t ht]
  exact product_eq t ht _ _ _ Wbabbb_product

def Wbbabb : CodeMatrix 14 :=
  !![1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0;
    2, 0, 1, 2, 0, 0, 2, 1, 0, 0, 2, 2, 2, 2;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 2, 3, 1, 0, 1, 1, 2, 3, 3, 2, 3;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

theorem Wbbabb_product : codeProduct FourteenData.B Wbabb = Wbbabb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbabb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, false, true, true] =
      evalMatrix t Wbbabb := by
  rw [word_cons, Wbabb_eval t ht]
  exact product_eq t ht _ _ _ Wbbabb_product

def Waaabaa : CodeMatrix 14 :=
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

theorem Waaabaa_product : codeProduct FourteenData.A Waabaa = Waaabaa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Waaabaa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, false, false, true, false, false] =
      evalMatrix t Waaabaa := by
  rw [word_cons, Waabaa_eval t ht]
  exact product_eq t ht _ _ _ Waaabaa_product

def Wabbabb : CodeMatrix 14 :=
  !![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0;
    2, 0, 1, 2, 0, 0, 2, 1, 0, 0, 2, 2, 2, 2;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 2, 2, 3, 1, 0, 1, 1, 2, 3, 3, 2, 3;
    1, 2, 2, 1, 2, 3, 0, 1, 2, 3, 1, 2, 2, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 1, 2, 0, 3, 0, 0, 1, 2, 0, 2, 0, 1, 1]

theorem Wabbabb_product : codeProduct FourteenData.A Wbbabb = Wabbabb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbabb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true, true] =
      evalMatrix t Wabbabb := by
  rw [word_cons, Wbbabb_eval t ht]
  exact product_eq t ht _ _ _ Wabbabb_product

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

def Wababbab : CodeMatrix 14 :=
  !![0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 3, 0, 2, 0, 2, 1, 1, 3, 1, 3, 1, 0, 2;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, 1, 2, 0, 2, 3, 3, 0, 2, 2, 2;
    0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 2, 0, 0, 2, 0, 2, 3, 1, 2;
    3, 1, 1, 2, 1, 3, 0, 0, 3, 1, 2, 3, 0, 1;
    3, 2, 1, 0, 0, 2, 1, 1, 3, 1, 3, 1, 1, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 2, 1, 3, 2, 0, 1, 1, 1, 0, 0, 3]

theorem Wababbab_product : codeProduct FourteenData.A Wbabbab = Wababbab :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wababbab_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, true, false, true] =
      evalMatrix t Wababbab := by
  rw [word_cons, Wbabbab_eval t ht]
  exact product_eq t ht _ _ _ Wababbab_product

def Wbaaabaa : CodeMatrix 14 :=
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

theorem Wbaaabaa_product : codeProduct FourteenData.B Waaabaa = Wbaaabaa :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbaaabaa_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, false, false, true, false, false] =
      evalMatrix t Wbaaabaa := by
  rw [word_cons, Waaabaa_eval t ht]
  exact product_eq t ht _ _ _ Wbaaabaa_product

end AlgebraWords

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
