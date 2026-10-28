module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate.AlgebraWords

/-!
# The rank-one polynomial

The stated linear combination gives T, and constant-first Horner
evaluation of the supplied degree-thirteen polynomial gives v times lam.
Every dense multiplication is checked against a literal intermediate matrix.
Source: ATLAS J2G1-f4r14aB0 and the witnesses retained in ../source/.
Generated literal proposals are certified by Lean kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
open Arithmetic
variable {F : Type*} [Field F] [CharP F 2]

open AlgebraWords

def T : CodeMatrix 14 :=
  !![0, 2, 2, 3, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 3, 2, 3, 2, 0, 3, 0, 0, 0, 0, 1, 0, 0;
    3, 2, 2, 3, 2, 0, 3, 0, 0, 3, 0, 0, 0, 1;
    3, 2, 0, 0, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0;
    1, 2, 3, 1, 3, 3, 0, 0, 2, 3, 2, 1, 3, 1;
    3, 3, 0, 2, 0, 0, 0, 0, 2, 3, 1, 1, 0, 0;
    1, 0, 2, 0, 1, 1, 3, 2, 3, 0, 0, 2, 2, 2;
    1, 0, 3, 1, 1, 0, 1, 2, 0, 0, 1, 1, 2, 3;
    3, 3, 0, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1, 3;
    1, 0, 3, 0, 0, 2, 3, 0, 2, 0, 2, 3, 1, 2;
    3, 1, 0, 3, 0, 0, 2, 3, 0, 0, 0, 1, 1, 3;
    3, 2, 0, 3, 1, 0, 1, 1, 1, 3, 2, 2, 0, 0;
    0, 3, 3, 0, 2, 1, 1, 1, 0, 2, 1, 0, 2, 1;
    1, 3, 2, 3, 0, 1, 1, 3, 3, 2, 3, 3, 3, 0]

theorem T_code : (codeAdd (codeScale 3 Wbabbb) (codeAdd (codeScale 3 Wabbabb) (codeAdd (codeScale 2 Wbaaabaa) (codeScale 1 Wababbab)))) = T :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem T_eval (t : F) (ht : t ^ 2 = t + 1) :
    algebraValue t (evalMatrix t FourteenData.A) (evalMatrix t FourteenData.B)
      FourteenData.algebraCoefficients FourteenData.algebraWords = evalMatrix t T := by
  simp only [FourteenData.algebraCoefficients, FourteenData.algebraWords, algebraValue]
  have hz : coefficient t 0 = 0 := rfl
  simp only [hz, zero_smul, zero_add, add_zero]
  rw [Wbabbb_eval t ht, Wabbabb_eval t ht, Wbaaabaa_eval t ht, Wababbab_eval t ht]
  simpa only [eval_add, eval_scale t ht] using congrArg (evalMatrix t) T_code

def H12 : CodeMatrix 14 :=
  !![1, 2, 2, 3, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 2, 2, 3, 2, 0, 3, 0, 0, 0, 0, 1, 0, 0;
    3, 2, 3, 3, 2, 0, 3, 0, 0, 3, 0, 0, 0, 1;
    3, 2, 0, 1, 0, 3, 0, 2, 0, 0, 0, 1, 0, 0;
    1, 2, 3, 1, 2, 3, 0, 0, 2, 3, 2, 1, 3, 1;
    3, 3, 0, 2, 0, 1, 0, 0, 2, 3, 1, 1, 0, 0;
    1, 0, 2, 0, 1, 1, 2, 2, 3, 0, 0, 2, 2, 2;
    1, 0, 3, 1, 1, 0, 1, 3, 0, 0, 1, 1, 2, 3;
    3, 3, 0, 0, 2, 3, 1, 2, 3, 0, 3, 1, 1, 3;
    1, 0, 3, 0, 0, 2, 3, 0, 2, 1, 2, 3, 1, 2;
    3, 1, 0, 3, 0, 0, 2, 3, 0, 0, 1, 1, 1, 3;
    3, 2, 0, 3, 1, 0, 1, 1, 1, 3, 2, 3, 0, 0;
    0, 3, 3, 0, 2, 1, 1, 1, 0, 2, 1, 0, 3, 1;
    1, 3, 2, 3, 0, 1, 1, 3, 3, 2, 3, 3, 3, 1]

def H11 : CodeMatrix 14 :=
  !![0, 2, 0, 3, 0, 0, 1, 0, 0, 0, 3, 1, 2, 1;
    1, 1, 0, 1, 3, 0, 3, 1, 0, 3, 1, 0, 0, 1;
    3, 0, 0, 0, 2, 0, 2, 3, 3, 1, 1, 0, 0, 1;
    0, 2, 3, 0, 2, 3, 2, 0, 0, 1, 3, 3, 3, 1;
    0, 1, 3, 2, 0, 0, 3, 1, 2, 1, 2, 0, 0, 3;
    0, 1, 2, 2, 1, 2, 1, 2, 1, 0, 3, 0, 0, 3;
    2, 1, 2, 3, 3, 3, 0, 0, 3, 0, 3, 1, 2, 1;
    1, 3, 0, 1, 1, 0, 0, 0, 2, 0, 3, 1, 0, 3;
    3, 0, 0, 2, 3, 0, 2, 0, 0, 3, 1, 1, 0, 0;
    1, 2, 1, 0, 3, 3, 2, 0, 2, 3, 0, 1, 3, 1;
    0, 1, 0, 0, 2, 2, 0, 2, 2, 0, 1, 0, 3, 3;
    0, 3, 2, 0, 3, 2, 0, 1, 1, 1, 0, 3, 3, 3;
    3, 3, 1, 1, 0, 1, 3, 3, 2, 3, 0, 0, 3, 3;
    3, 0, 1, 2, 0, 0, 1, 2, 3, 3, 2, 2, 3, 1]

def H10 : CodeMatrix 14 :=
  !![3, 3, 2, 3, 0, 0, 1, 1, 1, 2, 3, 1, 1, 2;
    3, 0, 0, 2, 1, 2, 1, 1, 1, 0, 2, 2, 0, 3;
    2, 2, 0, 3, 3, 2, 1, 3, 2, 3, 3, 3, 3, 0;
    0, 2, 3, 3, 3, 3, 1, 2, 1, 0, 3, 2, 2, 1;
    3, 0, 3, 3, 2, 2, 3, 0, 1, 3, 0, 2, 0, 3;
    1, 2, 0, 2, 3, 3, 0, 0, 2, 2, 3, 0, 2, 1;
    0, 0, 3, 3, 1, 1, 2, 2, 3, 3, 3, 1, 2, 3;
    1, 2, 1, 3, 3, 2, 3, 0, 2, 1, 3, 3, 0, 2;
    3, 0, 2, 1, 3, 0, 0, 2, 0, 1, 2, 0, 3, 2;
    0, 0, 0, 3, 1, 2, 0, 1, 1, 3, 0, 1, 2, 2;
    0, 1, 1, 1, 3, 0, 1, 2, 1, 0, 3, 2, 2, 2;
    1, 3, 3, 2, 1, 3, 3, 2, 3, 0, 3, 2, 3, 0;
    2, 1, 0, 0, 3, 0, 0, 0, 0, 0, 3, 0, 2, 1;
    1, 2, 2, 0, 1, 1, 0, 0, 2, 1, 2, 2, 1, 3]

def H9 : CodeMatrix 14 :=
  !![3, 1, 3, 0, 1, 0, 2, 0, 2, 3, 3, 0, 3, 0;
    1, 3, 2, 3, 1, 3, 1, 0, 0, 2, 3, 3, 2, 2;
    0, 2, 0, 3, 3, 2, 0, 3, 0, 0, 2, 1, 2, 2;
    3, 3, 0, 1, 0, 1, 3, 3, 0, 2, 1, 3, 1, 0;
    2, 1, 3, 2, 3, 1, 2, 2, 1, 2, 2, 3, 0, 2;
    0, 3, 1, 1, 2, 0, 0, 3, 3, 1, 1, 2, 1, 1;
    1, 1, 2, 0, 1, 1, 3, 3, 2, 3, 0, 0, 1, 3;
    2, 2, 0, 0, 3, 2, 1, 1, 3, 1, 0, 2, 2, 2;
    1, 0, 3, 2, 0, 2, 2, 2, 0, 1, 3, 3, 2, 0;
    2, 3, 0, 1, 2, 3, 3, 3, 2, 3, 2, 1, 1, 2;
    2, 1, 3, 3, 2, 3, 3, 2, 3, 0, 2, 3, 3, 2;
    0, 2, 3, 2, 3, 0, 3, 3, 2, 3, 1, 0, 0, 1;
    0, 0, 0, 0, 2, 1, 1, 3, 2, 3, 0, 0, 3, 3;
    0, 0, 0, 2, 3, 2, 2, 3, 1, 3, 0, 1, 2, 2]

def H8 : CodeMatrix 14 :=
  !![3, 1, 2, 0, 2, 2, 2, 1, 1, 0, 1, 3, 3, 0;
    1, 2, 2, 1, 3, 3, 3, 1, 1, 2, 0, 3, 2, 2;
    3, 0, 3, 1, 0, 0, 0, 3, 2, 0, 1, 2, 3, 2;
    3, 1, 1, 2, 2, 2, 2, 3, 0, 3, 1, 3, 1, 2;
    3, 1, 2, 1, 3, 3, 0, 2, 1, 2, 2, 0, 2, 3;
    1, 1, 2, 1, 0, 0, 2, 1, 1, 3, 1, 2, 2, 3;
    2, 3, 3, 3, 0, 2, 3, 0, 2, 2, 3, 0, 2, 1;
    2, 3, 2, 1, 0, 3, 1, 2, 1, 2, 2, 0, 2, 0;
    3, 2, 3, 0, 2, 3, 2, 0, 1, 2, 1, 1, 1, 3;
    1, 1, 2, 0, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1;
    2, 3, 0, 3, 1, 3, 3, 2, 3, 1, 1, 3, 2, 1;
    0, 1, 3, 3, 3, 1, 1, 0, 2, 2, 1, 1, 1, 0;
    2, 1, 0, 1, 1, 0, 0, 1, 2, 2, 0, 0, 2, 1;
    3, 2, 3, 1, 3, 3, 0, 1, 0, 0, 3, 3, 0, 0]

def H7 : CodeMatrix 14 :=
  !![2, 2, 3, 1, 1, 3, 1, 0, 0, 2, 1, 1, 1, 3;
    0, 2, 1, 3, 1, 2, 0, 3, 1, 3, 1, 2, 0, 1;
    3, 2, 2, 0, 0, 3, 2, 3, 0, 1, 3, 0, 2, 0;
    0, 3, 3, 1, 3, 0, 2, 1, 2, 0, 2, 3, 2, 1;
    2, 2, 2, 3, 3, 0, 2, 2, 3, 3, 0, 1, 1, 3;
    0, 2, 1, 0, 2, 3, 0, 0, 2, 2, 0, 0, 3, 1;
    2, 0, 0, 3, 2, 0, 2, 0, 2, 2, 1, 2, 2, 0;
    3, 2, 2, 0, 1, 0, 3, 3, 3, 0, 3, 1, 3, 2;
    2, 1, 2, 0, 2, 1, 3, 0, 0, 1, 1, 2, 0, 0;
    3, 2, 3, 3, 1, 1, 2, 1, 3, 3, 0, 0, 3, 1;
    3, 0, 1, 3, 3, 1, 0, 3, 2, 2, 2, 0, 2, 0;
    2, 0, 1, 0, 0, 2, 3, 3, 1, 2, 1, 3, 3, 2;
    1, 3, 3, 1, 1, 1, 2, 2, 1, 2, 0, 2, 0, 2;
    1, 2, 2, 2, 0, 1, 0, 1, 3, 0, 2, 3, 3, 0]

def H6 : CodeMatrix 14 :=
  !![1, 3, 3, 0, 2, 0, 0, 1, 0, 3, 3, 1, 2, 1;
    1, 0, 0, 2, 1, 2, 3, 0, 3, 2, 1, 3, 2, 3;
    1, 3, 1, 2, 0, 2, 2, 2, 2, 0, 0, 2, 3, 1;
    2, 0, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2;
    1, 0, 3, 1, 2, 3, 1, 2, 3, 3, 1, 0, 2, 1;
    1, 2, 1, 2, 2, 2, 3, 3, 1, 3, 2, 3, 3, 2;
    3, 3, 1, 1, 0, 1, 3, 2, 0, 3, 0, 1, 0, 2;
    1, 1, 0, 0, 0, 3, 3, 3, 1, 3, 3, 1, 3, 3;
    0, 1, 1, 1, 0, 0, 3, 0, 0, 2, 3, 0, 0, 0;
    1, 2, 2, 0, 0, 2, 0, 1, 2, 2, 1, 2, 0, 2;
    0, 2, 3, 2, 1, 0, 2, 0, 3, 1, 0, 0, 2, 1;
    0, 0, 2, 2, 3, 2, 2, 0, 2, 2, 2, 0, 2, 2;
    1, 3, 1, 2, 0, 0, 3, 3, 3, 0, 3, 0, 2, 0;
    3, 3, 3, 3, 1, 0, 1, 1, 0, 1, 0, 1, 2, 2]

def H5 : CodeMatrix 14 :=
  !![0, 1, 1, 2, 1, 3, 0, 0, 0, 1, 0, 1, 3, 3;
    0, 1, 1, 2, 2, 1, 0, 3, 0, 2, 0, 1, 3, 0;
    2, 3, 1, 1, 0, 0, 0, 2, 0, 0, 2, 1, 0, 1;
    0, 1, 3, 2, 1, 1, 0, 0, 2, 0, 2, 2, 3, 0;
    1, 1, 0, 0, 0, 3, 3, 0, 2, 0, 0, 2, 1, 0;
    0, 3, 2, 1, 3, 2, 1, 1, 3, 3, 3, 2, 1, 0;
    0, 3, 3, 1, 1, 3, 2, 0, 1, 0, 1, 2, 0, 0;
    0, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 1, 2, 0;
    3, 0, 0, 2, 3, 3, 2, 1, 3, 3, 3, 3, 0, 1;
    2, 3, 3, 2, 3, 0, 0, 1, 0, 0, 3, 0, 2, 0;
    2, 1, 2, 1, 1, 3, 1, 0, 3, 0, 1, 1, 2, 3;
    0, 3, 1, 1, 3, 3, 0, 1, 2, 2, 2, 2, 1, 3;
    2, 1, 3, 3, 2, 2, 0, 2, 3, 0, 3, 2, 1, 0;
    1, 3, 2, 0, 3, 2, 0, 3, 3, 2, 0, 1, 0, 1]

def H4 : CodeMatrix 14 :=
  !![0, 0, 3, 1, 3, 0, 2, 3, 2, 1, 0, 2, 1, 1;
    1, 2, 0, 0, 2, 0, 0, 0, 3, 3, 3, 0, 3, 1;
    1, 2, 3, 3, 1, 2, 0, 2, 2, 2, 3, 1, 2, 1;
    0, 2, 2, 2, 0, 0, 1, 0, 1, 2, 2, 0, 2, 1;
    1, 2, 2, 0, 1, 3, 0, 1, 2, 1, 0, 3, 1, 1;
    2, 2, 0, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 0;
    1, 0, 0, 2, 1, 1, 0, 2, 2, 2, 1, 0, 0, 1;
    2, 0, 2, 1, 3, 2, 2, 2, 2, 0, 2, 1, 3, 3;
    3, 2, 3, 2, 1, 3, 2, 1, 1, 0, 2, 3, 3, 2;
    3, 0, 3, 1, 1, 1, 2, 1, 1, 3, 2, 2, 0, 3;
    1, 3, 3, 1, 1, 2, 0, 3, 2, 1, 1, 0, 2, 2;
    0, 0, 1, 0, 3, 1, 0, 3, 0, 1, 1, 3, 2, 3;
    0, 3, 3, 0, 0, 0, 2, 2, 3, 1, 3, 1, 0, 1;
    2, 0, 3, 3, 0, 2, 2, 2, 2, 3, 0, 3, 1, 2]

def H3 : CodeMatrix 14 :=
  !![1, 0, 0, 0, 1, 0, 3, 3, 0, 1, 0, 3, 2, 3;
    0, 2, 2, 1, 1, 0, 3, 3, 0, 2, 0, 0, 0, 0;
    1, 2, 2, 2, 1, 0, 1, 3, 3, 2, 3, 0, 3, 1;
    0, 2, 0, 0, 0, 3, 3, 3, 1, 0, 1, 3, 3, 3;
    0, 0, 0, 3, 1, 0, 3, 0, 2, 2, 0, 3, 3, 2;
    1, 2, 0, 1, 0, 3, 1, 3, 2, 0, 3, 2, 3, 2;
    0, 3, 3, 2, 1, 1, 0, 3, 3, 2, 0, 0, 2, 1;
    0, 3, 3, 2, 3, 2, 2, 2, 3, 1, 3, 3, 1, 0;
    1, 1, 1, 2, 0, 2, 3, 0, 0, 3, 0, 0, 1, 3;
    3, 3, 0, 0, 3, 3, 3, 0, 2, 0, 1, 0, 0, 1;
    3, 0, 2, 0, 3, 3, 0, 0, 1, 0, 1, 2, 2, 2;
    3, 3, 1, 2, 3, 1, 3, 1, 0, 2, 0, 2, 2, 3;
    1, 3, 3, 0, 0, 3, 2, 1, 0, 3, 3, 0, 0, 3;
    3, 0, 2, 1, 2, 3, 1, 1, 2, 0, 1, 2, 2, 2]

def H2 : CodeMatrix 14 :=
  !![2, 2, 1, 1, 0, 3, 0, 3, 3, 3, 2, 2, 3, 2;
    1, 1, 1, 2, 3, 0, 0, 2, 3, 2, 2, 1, 1, 3;
    0, 1, 3, 0, 2, 0, 1, 3, 0, 1, 0, 3, 0, 3;
    3, 0, 3, 3, 3, 0, 0, 3, 0, 0, 3, 0, 3, 0;
    3, 0, 2, 2, 2, 1, 3, 2, 2, 3, 3, 0, 2, 1;
    3, 1, 0, 2, 2, 1, 1, 0, 2, 1, 0, 3, 2, 0;
    3, 1, 3, 3, 2, 0, 1, 2, 1, 3, 0, 3, 3, 3;
    2, 3, 0, 2, 2, 0, 0, 1, 3, 1, 1, 3, 1, 1;
    0, 0, 3, 2, 2, 1, 2, 1, 1, 1, 0, 1, 2, 0;
    1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 0, 1, 3, 0;
    3, 0, 2, 2, 0, 1, 0, 0, 1, 0, 2, 1, 0, 3;
    0, 0, 3, 0, 0, 2, 0, 2, 2, 1, 1, 3, 2, 1;
    1, 2, 1, 3, 0, 0, 0, 1, 3, 1, 1, 0, 0, 0;
    3, 2, 0, 2, 2, 2, 1, 3, 1, 3, 0, 1, 0, 2]

def H1 : CodeMatrix 14 :=
  !![3, 0, 3, 0, 1, 1, 0, 3, 2, 2, 2, 0, 3, 2;
    2, 3, 2, 2, 1, 0, 0, 2, 0, 1, 3, 3, 2, 2;
    2, 2, 1, 0, 3, 1, 2, 2, 3, 0, 1, 2, 1, 3;
    2, 1, 2, 3, 3, 3, 3, 1, 1, 1, 1, 3, 1, 3;
    1, 1, 2, 0, 0, 0, 3, 1, 2, 2, 1, 1, 1, 0;
    3, 0, 2, 3, 3, 1, 0, 3, 0, 3, 2, 1, 3, 1;
    0, 3, 1, 3, 3, 0, 1, 0, 2, 1, 3, 3, 1, 3;
    1, 3, 2, 2, 0, 0, 2, 3, 0, 3, 1, 3, 1, 3;
    0, 2, 2, 0, 3, 1, 3, 3, 0, 0, 2, 3, 3, 2;
    0, 1, 0, 0, 3, 3, 3, 3, 3, 0, 3, 3, 0, 3;
    1, 3, 3, 1, 2, 1, 1, 3, 3, 0, 3, 3, 1, 0;
    1, 3, 0, 1, 0, 0, 3, 1, 2, 0, 3, 3, 1, 0;
    0, 3, 3, 3, 2, 2, 1, 1, 3, 3, 1, 0, 0, 1;
    1, 1, 2, 3, 1, 1, 1, 2, 0, 0, 3, 2, 1, 1]

theorem H12_step : codeAdd (codeScale 1 codeOne) (codeProduct T codeOne) =
    H12 := checkMatrix_sound _ _ (by decide +kernel)

theorem H11_step : codeAdd (codeScale 3 codeOne) (codeProduct T H12) =
    H11 := checkMatrix_sound _ _ (by decide +kernel)

theorem H10_step : codeAdd (codeScale 0 codeOne) (codeProduct T H11) =
    H10 := checkMatrix_sound _ _ (by decide +kernel)

theorem H9_step : codeAdd (codeScale 2 codeOne) (codeProduct T H10) =
    H9 := checkMatrix_sound _ _ (by decide +kernel)

theorem H8_step : codeAdd (codeScale 2 codeOne) (codeProduct T H9) =
    H8 := checkMatrix_sound _ _ (by decide +kernel)

theorem H7_step : codeAdd (codeScale 1 codeOne) (codeProduct T H8) =
    H7 := checkMatrix_sound _ _ (by decide +kernel)

theorem H6_step : codeAdd (codeScale 3 codeOne) (codeProduct T H7) =
    H6 := checkMatrix_sound _ _ (by decide +kernel)

theorem H5_step : codeAdd (codeScale 2 codeOne) (codeProduct T H6) =
    H5 := checkMatrix_sound _ _ (by decide +kernel)

theorem H4_step : codeAdd (codeScale 0 codeOne) (codeProduct T H5) =
    H4 := checkMatrix_sound _ _ (by decide +kernel)

theorem H3_step : codeAdd (codeScale 2 codeOne) (codeProduct T H4) =
    H3 := checkMatrix_sound _ _ (by decide +kernel)

theorem H2_step : codeAdd (codeScale 3 codeOne) (codeProduct T H3) =
    H2 := checkMatrix_sound _ _ (by decide +kernel)

theorem H1_step : codeAdd (codeScale 1 codeOne) (codeProduct T H2) =
    H1 := checkMatrix_sound _ _ (by decide +kernel)

theorem H0_step : codeAdd (codeScale 3 codeOne) (codeProduct T H1) =
    (codeOuter FourteenData.v FourteenData.lam) := checkMatrix_sound _ _ (by decide +kernel)

theorem polynomial_eq (t : F) (ht : t ^ 2 = t + 1) :
    polynomialValue t (evalMatrix t T) FourteenData.polynomial =
      Matrix.vecMulVec (evalVector t FourteenData.v) (evalVector t FourteenData.lam) := by
  have h13 : polynomialValue t (evalMatrix t T) [1] = evalMatrix t (codeOne : CodeMatrix 14) := by
    simp only [polynomialValue, mul_zero, add_zero, eval_one]
    change (1 : F) • (1 : Matrix (Fin 14) (Fin 14) F) = 1
    exact one_smul _ _
  have h12 : polynomialValue t (evalMatrix t T) [1, 1] = evalMatrix t H12 := by
    change coefficient t 1 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [1] = _
    rw [h13]
    exact horner_step t ht _ _ _ _ H12_step
  have h11 : polynomialValue t (evalMatrix t T) [3, 1, 1] = evalMatrix t H11 := by
    change coefficient t 3 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [1, 1] = _
    rw [h12]
    exact horner_step t ht _ _ _ _ H11_step
  have h10 : polynomialValue t (evalMatrix t T) [0, 3, 1, 1] = evalMatrix t H10 := by
    change coefficient t 0 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [3, 1, 1] = _
    rw [h11]
    exact horner_step t ht _ _ _ _ H10_step
  have h9 : polynomialValue t (evalMatrix t T) [2, 0, 3, 1, 1] = evalMatrix t H9 := by
    change coefficient t 2 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [0, 3, 1, 1] = _
    rw [h10]
    exact horner_step t ht _ _ _ _ H9_step
  have h8 : polynomialValue t (evalMatrix t T) [2, 2, 0, 3, 1, 1] = evalMatrix t H8 := by
    change coefficient t 2 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [2, 0, 3, 1, 1] = _
    rw [h9]
    exact horner_step t ht _ _ _ _ H8_step
  have h7 : polynomialValue t (evalMatrix t T) [1, 2, 2, 0, 3, 1, 1] = evalMatrix t H7 := by
    change coefficient t 1 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [2, 2, 0, 3, 1, 1] = _
    rw [h8]
    exact horner_step t ht _ _ _ _ H7_step
  have h6 : polynomialValue t (evalMatrix t T) [3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H6 := by
    change coefficient t 3 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [1, 2, 2, 0, 3, 1, 1] = _
    rw [h7]
    exact horner_step t ht _ _ _ _ H6_step
  have h5 : polynomialValue t (evalMatrix t T) [2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H5 := by
    change coefficient t 2 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h6]
    exact horner_step t ht _ _ _ _ H5_step
  have h4 : polynomialValue t (evalMatrix t T) [0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H4 := by
    change coefficient t 0 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [2, 3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h5]
    exact horner_step t ht _ _ _ _ H4_step
  have h3 : polynomialValue t (evalMatrix t T) [2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H3 := by
    change coefficient t 2 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h4]
    exact horner_step t ht _ _ _ _ H3_step
  have h2 : polynomialValue t (evalMatrix t T) [3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H2 := by
    change coefficient t 3 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h3]
    exact horner_step t ht _ _ _ _ H2_step
  have h1 : polynomialValue t (evalMatrix t T) [1, 3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t H1 := by
    change coefficient t 1 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h2]
    exact horner_step t ht _ _ _ _ H1_step
  have h0 : polynomialValue t (evalMatrix t T) [3, 1, 3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = evalMatrix t (codeOuter FourteenData.v FourteenData.lam) := by
    change coefficient t 3 • 1 + evalMatrix t T * polynomialValue t (evalMatrix t T) [1, 3, 2, 0, 2, 3, 1, 2, 2, 0, 3, 1, 1] = _
    rw [h1]
    exact horner_step t ht _ _ _ _ H0_step
  exact h0.trans (eval_outer t ht _ _)

theorem rankOne_mem (t : F) (ht : t ^ 2 = t + 1) :
    Matrix.vecMulVec (evalVector t FourteenData.v) (evalVector t FourteenData.lam) ∈
      Algebra.adjoin F ({evalMatrix t FourteenData.A, evalMatrix t FourteenData.B} :
        Set (Matrix (Fin 14) (Fin 14) F)) := by
  let S := Algebra.adjoin F ({evalMatrix t FourteenData.A, evalMatrix t FourteenData.B} :
    Set (Matrix (Fin 14) (Fin 14) F))
  have hT : evalMatrix t T ∈ S := by
    rw [← T_eval t ht]
    exact algebraValue_mem t S _ _ (Algebra.subset_adjoin (by simp))
      (Algebra.subset_adjoin (by simp)) _ _
  rw [← polynomial_eq t ht]
  exact polynomialValue_mem t S _ hT _

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate
