module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.Evaluation

/-!
# RelationWords: checked positive words

The bases of the order-seven, order-twelve and order-six relations
are evaluated in the exact positive-word convention of MatrixRelations.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

namespace RelationWords

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

def Wababb : CodeMatrix 14 :=
  !![1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 1;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 1, 0, 3, 1, 2, 2, 2, 1, 1, 1, 0]

theorem Wababb_product : codeProduct FourteenData.A Wbabb = Wababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, true] =
      evalMatrix t Wababb := by
  rw [word_cons, Wbabb_eval t ht]
  exact product_eq t ht _ _ _ Wababb_product

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

def Wbababb : CodeMatrix 14 :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    1, 2, 0, 2, 0, 2, 1, 0, 2, 1, 2, 2, 3, 1;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    1, 1, 0, 1, 0, 3, 1, 2, 2, 2, 1, 1, 1, 0;
    3, 1, 2, 0, 0, 1, 2, 1, 1, 3, 0, 2, 1, 3]

theorem Wbababb_product : codeProduct FourteenData.B Wababb = Wbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, false, true, true] =
      evalMatrix t Wbababb := by
  rw [word_cons, Wababb_eval t ht]
  exact product_eq t ht _ _ _ Wbababb_product

def Wbbababb : CodeMatrix 14 :=
  !![1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 2, 0, 0, 1, 2, 1, 1, 3, 0, 2, 1, 3;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem Wbbababb_product : codeProduct FourteenData.B Wbababb = Wbbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, true, false, true, false, true, true] =
      evalMatrix t Wbbababb := by
  rw [word_cons, Wbababb_eval t ht]
  exact product_eq t ht _ _ _ Wbbababb_product

def Wabbababb : CodeMatrix 14 :=
  !![1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0;
    3, 1, 2, 0, 0, 1, 2, 1, 1, 3, 0, 2, 1, 3;
    2, 0, 2, 0, 1, 1, 2, 0, 0, 2, 1, 3, 1, 3;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 3, 3, 1, 3, 2, 0, 1, 0, 3, 1, 2, 3]

theorem Wabbababb_product : codeProduct FourteenData.A Wbbababb = Wabbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, true, false, true, false, true, true] =
      evalMatrix t Wabbababb := by
  rw [word_cons, Wbbababb_eval t ht]
  exact product_eq t ht _ _ _ Wabbababb_product

def Wbabbababb : CodeMatrix 14 :=
  !![3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    2, 0, 1, 2, 0, 0, 2, 1, 0, 0, 2, 2, 2, 2;
    2, 0, 1, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 2, 0, 0, 1, 2, 1, 1, 3, 0, 2, 1, 3;
    2, 0, 2, 0, 1, 1, 2, 0, 0, 2, 1, 3, 1, 3;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    1, 3, 0, 3, 1, 2, 1, 3, 3, 2, 0, 1, 3, 3;
    3, 1, 3, 3, 1, 3, 2, 0, 1, 0, 3, 1, 2, 3;
    0, 2, 0, 0, 0, 3, 1, 2, 1, 1, 1, 3, 0, 1]

theorem Wbabbababb_product : codeProduct FourteenData.B Wabbababb = Wbabbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbabbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, true, false, true, false, true, true] =
      evalMatrix t Wbabbababb := by
  rw [word_cons, Wabbababb_eval t ht]
  exact product_eq t ht _ _ _ Wbabbababb_product

def Wababbababb : CodeMatrix 14 :=
  !![2, 0, 1, 2, 0, 0, 2, 1, 0, 0, 2, 2, 2, 2;
    3, 0, 0, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    2, 0, 1, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    2, 0, 2, 0, 1, 1, 2, 0, 0, 2, 1, 3, 1, 3;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    3, 1, 2, 0, 0, 1, 2, 1, 1, 3, 0, 2, 1, 3;
    3, 1, 3, 3, 1, 3, 2, 0, 1, 0, 3, 1, 2, 3;
    2, 2, 0, 3, 1, 0, 2, 1, 2, 3, 2, 1, 1, 1;
    1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    2, 2, 1, 0, 0, 0, 1, 2, 3, 2, 1, 0, 2, 1]

theorem Wababbababb_product : codeProduct FourteenData.A Wbabbababb = Wababbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wababbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, true, false, true, false, true, true] =
      evalMatrix t Wababbababb := by
  rw [word_cons, Wbabbababb_eval t ht]
  exact product_eq t ht _ _ _ Wababbababb_product

def Wbababbababb : CodeMatrix 14 :=
  !![2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 3, 3, 2;
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 3, 3, 2;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    2, 0, 2, 0, 1, 1, 2, 0, 0, 2, 1, 3, 1, 3;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    2, 0, 1, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    3, 1, 3, 3, 1, 3, 2, 0, 1, 0, 3, 1, 2, 3;
    2, 2, 0, 3, 1, 0, 2, 1, 2, 3, 2, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0;
    2, 2, 1, 0, 0, 0, 1, 2, 3, 2, 1, 0, 2, 1;
    2, 0, 1, 1, 2, 0, 2, 2, 0, 0, 2, 1, 2, 2]

theorem Wbababbababb_product : codeProduct FourteenData.B Wababbababb = Wbababbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wbababbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [true, false, true, false, true, true, false, true, false, true, true] =
      evalMatrix t Wbababbababb := by
  rw [word_cons, Wababbababb_eval t ht]
  exact product_eq t ht _ _ _ Wbababbababb_product

def Wabababbababb : CodeMatrix 14 :=
  !![1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 3, 3, 2;
    2, 1, 0, 3, 0, 1, 2, 0, 0, 1, 3, 1, 1, 0;
    1, 3, 1, 2, 1, 2, 0, 0, 2, 1, 3, 3, 3, 1;
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 3, 3, 2;
    0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0;
    2, 0, 2, 0, 1, 1, 2, 0, 0, 2, 1, 3, 1, 3;
    2, 2, 0, 3, 1, 0, 2, 1, 2, 3, 2, 1, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    2, 0, 1, 2, 0, 0, 3, 1, 0, 0, 3, 2, 2, 2;
    3, 1, 3, 3, 1, 3, 2, 0, 1, 0, 3, 1, 2, 3;
    2, 2, 1, 0, 0, 0, 1, 2, 3, 2, 1, 0, 2, 1;
    3, 2, 0, 3, 0, 2, 1, 3, 2, 0, 2, 1, 2, 3;
    0, 2, 0, 3, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3;
    0, 1, 1, 3, 1, 2, 2, 0, 2, 2, 2, 0, 2, 0]

theorem Wabababbababb_product : codeProduct FourteenData.A Wbababbababb = Wabababbababb :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem Wabababbababb_eval (t : F) (ht : t ^ 2 = t + 1) :
    wordValue (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B) [false, true, false, true, false, true, true, false, true, false, true, true] =
      evalMatrix t Wabababbababb := by
  rw [word_cons, Wbababbababb_eval t ht]
  exact product_eq t ht _ _ _ Wabababbababb_product

end RelationWords

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
