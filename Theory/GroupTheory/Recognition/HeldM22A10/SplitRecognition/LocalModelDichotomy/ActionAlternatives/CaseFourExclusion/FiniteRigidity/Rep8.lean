module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Witnesses

/-!
# Case IV certificates with first column 8

The witnesses concern the literal Case IV matrices in `AutomizerData`, in
the ordered basis z₁,z₃,a,d. A singular tuple carries a nonzero kernel vector;
an invertible tuple carries a word fixing the first vector outside the eight
local matrices. The accompanying scripts generate data only: every assertion
below is checked by Lean's kernel, with no external computation axiom.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity

private def choice0 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2],
    ![.inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2, .inl 2]]

private theorem check0 : ∀ y z : Fin 16,
    Check ![8, 0, y, z] (choice0 y z) := by decide +kernel

private def choice1 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 10, .inl 12, .inl 14, .inr 8, .inr 40, .inr 12, .inr 18, .inl 9, .inl 11, .inl 13, .inl 15, .inr 31, .inr 53, .inr 54, .inr 23],
    ![.inl 8, .inl 10, .inl 14, .inl 12, .inr 12, .inr 17, .inr 8, .inr 40, .inl 9, .inl 11, .inl 15, .inl 13, .inr 54, .inr 23, .inr 31, .inr 53],
    ![.inl 8, .inl 10, .inr 5, .inr 27, .inl 12, .inl 14, .inr 7, .inr 55, .inl 9, .inl 11, .inr 26, .inr 8, .inl 13, .inl 15, .inr 56, .inr 8],
    ![.inl 8, .inl 10, .inr 4, .inr 27, .inl 14, .inl 12, .inr 35, .inr 7, .inl 9, .inl 11, .inr 26, .inr 8, .inl 15, .inl 13, .inr 9, .inr 12],
    ![.inl 8, .inl 10, .inr 4, .inr 27, .inr 7, .inr 55, .inl 12, .inl 14, .inl 9, .inl 11, .inr 26, .inr 8, .inr 56, .inr 12, .inl 13, .inl 15],
    ![.inl 8, .inl 10, .inr 5, .inr 27, .inr 35, .inr 7, .inl 14, .inl 12, .inl 9, .inl 11, .inr 26, .inr 8, .inr 57, .inr 8, .inl 15, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 10, .inl 13, .inl 15, .inr 40, .inr 8, .inr 18, .inr 12, .inl 9, .inl 11, .inl 12, .inl 14, .inr 53, .inr 31, .inr 23, .inr 17],
    ![.inl 8, .inl 10, .inl 15, .inl 13, .inr 18, .inr 12, .inr 24, .inr 8, .inl 9, .inl 11, .inl 14, .inl 12, .inr 17, .inr 54, .inr 58, .inr 31],
    ![.inl 8, .inl 10, .inr 4, .inr 27, .inl 13, .inl 15, .inr 56, .inr 57, .inl 9, .inl 11, .inr 26, .inr 8, .inl 12, .inl 14, .inr 7, .inr 35],
    ![.inl 8, .inl 10, .inr 5, .inr 27, .inl 15, .inl 13, .inr 57, .inr 56, .inl 9, .inl 11, .inr 26, .inr 8, .inl 14, .inl 12, .inr 8, .inr 7],
    ![.inl 8, .inl 10, .inr 5, .inr 27, .inr 56, .inr 57, .inl 13, .inl 15, .inl 9, .inl 11, .inr 26, .inr 8, .inr 7, .inr 35, .inl 12, .inl 14],
    ![.inl 8, .inl 10, .inr 4, .inr 27, .inr 57, .inr 56, .inl 15, .inl 13, .inl 9, .inl 11, .inr 26, .inr 8, .inr 12, .inr 7, .inl 14, .inl 12]]

private theorem check1 : ∀ y z : Fin 16,
    Check ![8, 1, y, z] (choice1 y z) := by decide +kernel

private def choice2 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 10, .inl 14, .inr 5, .inr 6, .inr 36, .inr 59, .inl 9, .inl 13, .inl 11, .inl 15, .inr 26, .inr 8, .inr 60, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 10, .inl 12, .inr 36, .inr 7, .inr 5, .inr 6, .inl 9, .inl 15, .inl 11, .inl 13, .inr 60, .inr 8, .inr 26, .inr 8],
    ![.inl 8, .inr 61, .inl 10, .inr 43, .inl 12, .inr 3, .inl 14, .inr 62, .inl 9, .inr 44, .inl 11, .inr 42, .inl 13, .inr 2, .inl 15, .inr 63],
    ![.inl 8, .inr 1, .inl 10, .inr 64, .inr 3, .inl 12, .inr 26, .inl 14, .inl 9, .inr 0, .inl 11, .inr 4, .inr 2, .inl 13, .inr 5, .inl 15],
    ![.inl 8, .inr 64, .inl 10, .inr 43, .inl 14, .inr 62, .inl 12, .inr 3, .inl 9, .inr 4, .inl 11, .inr 4, .inl 15, .inr 63, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inl 10, .inr 9, .inr 62, .inl 14, .inr 3, .inl 12, .inl 9, .inr 0, .inl 11, .inr 44, .inr 63, .inl 15, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 10, .inl 15, .inr 6, .inr 5, .inr 57, .inr 36, .inl 9, .inl 12, .inl 11, .inl 14, .inr 7, .inr 26, .inr 8, .inr 60],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 10, .inl 13, .inr 65, .inr 36, .inr 6, .inr 5, .inl 9, .inl 14, .inl 11, .inl 12, .inr 7, .inr 66, .inr 8, .inr 26],
    ![.inl 8, .inr 1, .inl 10, .inr 64, .inl 13, .inr 2, .inl 15, .inr 63, .inl 9, .inr 0, .inl 11, .inr 4, .inl 12, .inr 3, .inl 14, .inr 5],
    ![.inl 8, .inr 35, .inl 10, .inr 43, .inr 2, .inl 13, .inr 63, .inl 15, .inl 9, .inr 44, .inl 11, .inr 42, .inr 3, .inl 12, .inr 62, .inl 14],
    ![.inl 8, .inr 1, .inl 10, .inr 9, .inl 15, .inr 63, .inl 13, .inr 2, .inl 9, .inr 0, .inl 11, .inr 44, .inl 14, .inr 6, .inl 12, .inr 3],
    ![.inl 8, .inr 64, .inl 10, .inr 43, .inr 63, .inl 15, .inr 2, .inl 13, .inl 9, .inr 4, .inl 11, .inr 4, .inr 36, .inl 14, .inr 3, .inl 12]]

private theorem check2 : ∀ y z : Fin 16,
    Check ![8, 2, y, z] (choice2 y z) := by decide +kernel

private def choice3 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 14, .inl 10, .inr 4, .inr 6, .inr 44, .inr 36, .inl 9, .inl 13, .inl 15, .inl 11, .inr 26, .inr 8, .inr 9, .inr 10],
    ![.inl 8, .inl 14, .inl 12, .inl 10, .inr 7, .inr 36, .inr 4, .inr 6, .inl 9, .inl 15, .inl 13, .inl 11, .inr 56, .inr 10, .inr 26, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inl 12, .inr 64, .inr 26, .inl 14, .inl 9, .inr 0, .inr 42, .inl 11, .inl 13, .inr 4, .inr 5, .inl 15],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inr 3, .inl 12, .inl 14, .inr 64, .inl 9, .inr 0, .inr 42, .inl 11, .inr 2, .inl 13, .inl 15, .inr 4],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inr 67, .inl 14, .inl 12, .inr 3, .inl 9, .inr 0, .inr 42, .inl 11, .inr 6, .inl 15, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inl 14, .inr 62, .inr 67, .inl 12, .inl 9, .inr 0, .inr 42, .inl 11, .inl 15, .inr 63, .inr 6, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 15, .inl 10, .inr 6, .inr 4, .inr 36, .inr 44, .inl 9, .inl 12, .inl 14, .inl 11, .inr 7, .inr 26, .inr 10, .inr 9],
    ![.inl 8, .inl 15, .inl 13, .inl 10, .inr 36, .inr 44, .inr 6, .inr 4, .inl 9, .inl 14, .inl 12, .inl 11, .inr 66, .inr 7, .inr 8, .inr 26],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inl 13, .inr 2, .inr 64, .inl 15, .inl 9, .inr 0, .inr 42, .inl 11, .inl 12, .inr 3, .inr 4, .inl 14],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inr 64, .inl 13, .inl 15, .inr 63, .inl 9, .inr 0, .inr 42, .inl 11, .inr 4, .inl 12, .inl 14, .inr 5],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inr 63, .inl 15, .inl 13, .inr 35, .inl 9, .inr 0, .inr 42, .inl 11, .inr 62, .inl 14, .inl 12, .inr 6],
    ![.inl 8, .inr 1, .inr 43, .inl 10, .inl 15, .inr 67, .inr 2, .inl 13, .inl 9, .inr 0, .inr 42, .inl 11, .inl 14, .inr 6, .inr 3, .inl 12]]

private theorem check3 : ∀ y z : Fin 16,
    Check ![8, 3, y, z] (choice3 y z) := by decide +kernel

private def choice4 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 8, .inr 17, .inl 10, .inl 14, .inr 10, .inr 48, .inl 9, .inl 13, .inr 31, .inr 68, .inl 11, .inl 15, .inr 69, .inr 23],
    ![.inl 8, .inr 64, .inl 12, .inr 3, .inl 10, .inr 43, .inl 14, .inr 62, .inl 9, .inr 4, .inl 13, .inr 2, .inl 11, .inr 42, .inl 15, .inr 4],
    ![.inl 8, .inr 1, .inr 70, .inl 12, .inl 10, .inr 43, .inr 26, .inl 14, .inl 9, .inr 0, .inr 10, .inl 13, .inl 11, .inr 42, .inr 5, .inl 15],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 36, .inr 7, .inl 10, .inl 12, .inr 4, .inr 6, .inl 9, .inl 15, .inr 60, .inr 10, .inl 11, .inl 13, .inr 26, .inr 8],
    ![.inl 8, .inr 1, .inl 14, .inr 62, .inl 10, .inr 43, .inl 12, .inr 3, .inl 9, .inr 0, .inl 15, .inr 63, .inl 11, .inr 42, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inr 62, .inl 14, .inl 10, .inr 43, .inr 3, .inl 12, .inl 9, .inr 0, .inr 63, .inl 15, .inl 11, .inr 42, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 10, .inr 40, .inl 10, .inl 15, .inr 24, .inr 8, .inl 9, .inl 12, .inr 69, .inr 23, .inl 11, .inl 14, .inr 17, .inr 31],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inl 10, .inr 22, .inl 15, .inr 63, .inl 9, .inr 0, .inl 12, .inr 3, .inl 11, .inr 30, .inl 14, .inr 5],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inl 10, .inr 43, .inr 9, .inl 15, .inl 9, .inr 0, .inr 3, .inl 12, .inl 11, .inr 42, .inr 71, .inl 14],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 44, .inr 36, .inl 10, .inl 13, .inr 6, .inr 5, .inl 9, .inl 14, .inr 7, .inr 8, .inl 11, .inl 12, .inr 8, .inr 26],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inl 10, .inr 43, .inl 13, .inr 2, .inl 9, .inr 0, .inl 14, .inr 27, .inl 11, .inr 42, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inl 10, .inr 43, .inr 2, .inl 13, .inl 9, .inr 0, .inr 36, .inl 14, .inl 11, .inr 42, .inr 3, .inl 12]]

private theorem check4 : ∀ y z : Fin 16,
    Check ![8, 4, y, z] (choice4 y z) := by decide +kernel

private def choice5 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 10, .inr 40, .inl 14, .inl 10, .inr 8, .inr 17, .inl 9, .inl 13, .inr 69, .inr 23, .inl 15, .inl 11, .inr 31, .inr 53],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inr 70, .inl 10, .inr 26, .inl 14, .inl 9, .inr 0, .inl 13, .inr 2, .inr 44, .inl 11, .inr 5, .inl 15],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inr 43, .inl 10, .inl 14, .inr 9, .inl 9, .inr 0, .inr 2, .inl 13, .inr 42, .inl 11, .inl 15, .inr 66],
    ![.inl 8, .inl 14, .inr 7, .inr 36, .inl 12, .inl 10, .inr 5, .inr 6, .inl 9, .inl 15, .inr 56, .inr 8, .inl 13, .inl 11, .inr 26, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 1, .inr 62, .inl 14, .inr 43, .inl 10, .inl 12, .inr 3, .inl 9, .inr 0, .inr 63, .inl 15, .inr 42, .inl 11, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inl 14, .inr 62, .inr 43, .inl 10, .inr 3, .inl 12, .inl 9, .inr 0, .inl 15, .inr 63, .inr 42, .inl 11, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 8, .inr 24, .inl 15, .inl 10, .inr 48, .inr 10, .inl 9, .inl 12, .inr 31, .inr 17, .inl 14, .inl 11, .inr 23, .inr 69],
    ![.inl 8, .inr 64, .inl 13, .inr 2, .inr 43, .inl 10, .inr 63, .inl 15, .inl 9, .inr 4, .inl 12, .inr 3, .inr 42, .inl 11, .inr 4, .inl 14],
    ![.inl 8, .inr 1, .inr 35, .inl 13, .inr 43, .inl 10, .inl 15, .inr 63, .inl 9, .inr 0, .inr 30, .inl 12, .inr 42, .inl 11, .inl 14, .inr 5],
    ![.inl 8, .inl 15, .inr 36, .inr 65, .inl 13, .inl 10, .inr 6, .inr 4, .inl 9, .inl 14, .inr 66, .inr 7, .inl 12, .inl 11, .inr 8, .inr 26],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inr 43, .inl 10, .inl 13, .inr 2, .inl 9, .inr 0, .inr 62, .inl 14, .inr 42, .inl 11, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inr 43, .inl 10, .inr 2, .inl 13, .inl 9, .inr 0, .inl 14, .inr 27, .inr 42, .inl 11, .inr 3, .inl 12]]

private theorem check5 : ∀ y z : Fin 16,
    Check ![8, 5, y, z] (choice5 y z) := by decide +kernel

private def choice6 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 36, .inr 59, .inr 4, .inr 6, .inl 10, .inl 14, .inl 9, .inl 13, .inr 60, .inr 10, .inr 26, .inr 8, .inl 11, .inl 15],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inl 14, .inr 62, .inl 10, .inr 43, .inl 9, .inr 0, .inl 13, .inr 2, .inl 15, .inr 63, .inl 11, .inr 42],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inr 62, .inl 14, .inl 10, .inr 43, .inl 9, .inr 0, .inr 2, .inl 13, .inr 63, .inl 15, .inl 11, .inr 42],
    ![.inl 8, .inr 64, .inl 14, .inr 62, .inl 12, .inr 3, .inl 10, .inr 43, .inl 9, .inr 4, .inl 15, .inr 63, .inl 13, .inr 4, .inl 11, .inr 42],
    ![.inl 8, .inr 1, .inr 72, .inl 14, .inr 3, .inl 12, .inl 10, .inr 43, .inl 9, .inr 0, .inr 27, .inl 15, .inr 2, .inl 13, .inl 11, .inr 42],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 8, .inr 32, .inr 10, .inr 17, .inl 10, .inl 12, .inl 9, .inl 15, .inr 31, .inr 68, .inr 69, .inr 23, .inl 11, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 44, .inr 36, .inr 6, .inr 5, .inl 10, .inl 15, .inl 9, .inl 12, .inr 73, .inr 8, .inr 7, .inr 26, .inl 11, .inl 14],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inl 15, .inr 63, .inl 10, .inr 43, .inl 9, .inr 0, .inl 12, .inr 3, .inl 14, .inr 6, .inl 11, .inr 42],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inr 63, .inl 15, .inl 10, .inr 43, .inl 9, .inr 0, .inr 3, .inl 12, .inr 62, .inl 14, .inl 11, .inr 42],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inl 13, .inr 2, .inl 10, .inr 74, .inl 9, .inr 0, .inl 14, .inr 27, .inl 12, .inr 3, .inl 11, .inr 28],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inr 35, .inl 13, .inl 10, .inr 43, .inl 9, .inr 0, .inr 62, .inl 14, .inr 75, .inl 12, .inl 11, .inr 42],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 10, .inr 40, .inr 47, .inr 8, .inl 10, .inl 13, .inl 9, .inl 14, .inr 17, .inr 23, .inr 53, .inr 31, .inl 11, .inl 12]]

private theorem check6 : ∀ y z : Fin 16,
    Check ![8, 6, y, z] (choice6 y z) := by decide +kernel

private def choice7 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 44, .inr 36, .inr 5, .inr 6, .inl 14, .inl 10, .inl 9, .inl 13, .inr 57, .inr 8, .inr 26, .inr 8, .inl 15, .inl 11],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inr 62, .inl 14, .inr 43, .inl 10, .inl 9, .inr 0, .inl 13, .inr 2, .inr 63, .inl 15, .inr 42, .inl 11],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inl 14, .inr 62, .inr 43, .inl 10, .inl 9, .inr 0, .inr 2, .inl 13, .inl 15, .inr 63, .inr 42, .inl 11],
    ![.inl 8, .inr 1, .inr 62, .inl 14, .inl 12, .inr 9, .inr 43, .inl 10, .inl 9, .inr 0, .inr 63, .inl 15, .inl 13, .inr 35, .inr 42, .inl 11],
    ![.inl 8, .inr 1, .inl 14, .inr 62, .inr 3, .inl 12, .inr 72, .inl 10, .inl 9, .inr 0, .inl 15, .inr 63, .inr 2, .inl 13, .inr 27, .inl 11],
    ![.inl 8, .inl 14, .inr 10, .inr 40, .inr 8, .inr 47, .inl 12, .inl 10, .inl 9, .inl 15, .inr 69, .inr 23, .inr 31, .inr 53, .inl 13, .inl 11],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 36, .inr 57, .inr 6, .inr 4, .inl 15, .inl 10, .inl 9, .inl 12, .inr 60, .inr 10, .inr 7, .inr 26, .inl 14, .inl 11],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inr 63, .inl 15, .inr 43, .inl 10, .inl 9, .inr 0, .inl 12, .inr 3, .inr 62, .inl 14, .inr 42, .inl 11],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inl 15, .inr 63, .inr 43, .inl 10, .inl 9, .inr 0, .inr 3, .inl 12, .inl 14, .inr 6, .inr 42, .inl 11],
    ![.inl 8, .inr 1, .inr 74, .inl 15, .inl 13, .inr 2, .inr 43, .inl 10, .inl 9, .inr 0, .inr 28, .inl 14, .inl 12, .inr 3, .inr 42, .inl 11],
    ![.inl 8, .inr 64, .inl 15, .inr 63, .inr 2, .inl 13, .inr 43, .inl 10, .inl 9, .inr 4, .inl 14, .inr 27, .inr 3, .inl 12, .inr 42, .inl 11],
    ![.inl 8, .inl 15, .inr 8, .inr 24, .inr 48, .inr 10, .inl 13, .inl 10, .inl 9, .inl 14, .inr 31, .inr 16, .inr 17, .inr 69, .inl 12, .inl 11],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7]]

private theorem check7 : ∀ y z : Fin 16,
    Check ![8, 7, y, z] (choice7 y z) := by decide +kernel

private def choice8 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3],
    ![.inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3, .inl 3]]

private theorem check8 : ∀ y z : Fin 16,
    Check ![8, 8, y, z] (choice8 y z) := by decide +kernel

private def choice9 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 11, .inl 12, .inl 15, .inr 12, .inr 17, .inr 19, .inr 8, .inl 9, .inl 10, .inl 13, .inl 14, .inr 54, .inr 23, .inr 40, .inr 31],
    ![.inl 8, .inl 11, .inl 15, .inl 12, .inr 8, .inr 19, .inr 18, .inr 12, .inl 9, .inl 10, .inl 14, .inl 13, .inr 31, .inr 40, .inr 23, .inr 54],
    ![.inl 8, .inl 11, .inr 27, .inr 5, .inl 12, .inl 15, .inr 57, .inr 7, .inl 9, .inl 10, .inr 36, .inr 26, .inl 13, .inl 14, .inr 8, .inr 56],
    ![.inl 8, .inl 11, .inr 27, .inr 4, .inl 15, .inl 12, .inr 7, .inr 35, .inl 9, .inl 10, .inr 36, .inr 26, .inl 14, .inl 13, .inr 12, .inr 9],
    ![.inl 8, .inl 11, .inr 27, .inr 5, .inr 35, .inr 7, .inl 12, .inl 15, .inl 9, .inl 10, .inr 36, .inr 26, .inr 76, .inr 8, .inl 13, .inl 14],
    ![.inl 8, .inl 11, .inr 27, .inr 4, .inr 7, .inr 57, .inl 15, .inl 12, .inl 9, .inl 10, .inr 36, .inr 26, .inr 56, .inr 12, .inl 14, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 11, .inl 13, .inl 14, .inr 18, .inr 12, .inr 8, .inr 19, .inl 9, .inl 10, .inl 12, .inl 15, .inr 17, .inr 54, .inr 31, .inr 40],
    ![.inl 8, .inl 11, .inl 14, .inl 13, .inr 19, .inr 8, .inr 12, .inr 18, .inl 9, .inl 10, .inl 15, .inl 12, .inr 40, .inr 31, .inr 17, .inr 23],
    ![.inl 8, .inl 11, .inr 27, .inr 4, .inl 13, .inl 14, .inr 31, .inr 56, .inl 9, .inl 10, .inr 36, .inr 26, .inl 12, .inl 15, .inr 35, .inr 7],
    ![.inl 8, .inl 11, .inr 27, .inr 5, .inl 14, .inl 13, .inr 56, .inr 40, .inl 9, .inl 10, .inr 36, .inr 26, .inl 15, .inl 12, .inr 7, .inr 8],
    ![.inl 8, .inl 11, .inr 27, .inr 4, .inr 23, .inr 56, .inl 13, .inl 14, .inl 9, .inl 10, .inr 36, .inr 26, .inr 12, .inr 7, .inl 12, .inl 15],
    ![.inl 8, .inl 11, .inr 27, .inr 5, .inr 56, .inr 76, .inl 14, .inl 13, .inl 9, .inl 10, .inr 36, .inr 26, .inr 7, .inr 35, .inl 15, .inl 12]]

private theorem check9 : ∀ y z : Fin 16,
    Check ![8, 9, y, z] (choice9 y z) := by decide +kernel

private def choice10 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 11, .inl 15, .inr 4, .inr 6, .inr 60, .inr 57, .inl 9, .inl 13, .inl 10, .inl 14, .inr 26, .inr 8, .inr 36, .inr 44],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 11, .inl 12, .inr 7, .inr 66, .inr 6, .inr 4, .inl 9, .inl 14, .inl 10, .inl 13, .inr 44, .inr 36, .inr 8, .inr 26],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inl 12, .inr 64, .inl 15, .inr 63, .inl 9, .inr 0, .inl 10, .inr 43, .inl 13, .inr 4, .inl 14, .inr 5],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inr 3, .inl 12, .inr 64, .inl 15, .inl 9, .inr 0, .inl 10, .inr 43, .inr 2, .inl 13, .inr 4, .inl 14],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inl 15, .inr 63, .inl 12, .inr 52, .inl 9, .inr 0, .inl 10, .inr 43, .inl 14, .inr 6, .inl 13, .inr 29],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inr 52, .inl 15, .inr 3, .inl 12, .inl 9, .inr 0, .inl 10, .inr 43, .inr 29, .inl 14, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 11, .inl 14, .inr 6, .inr 4, .inr 31, .inr 60, .inl 9, .inl 12, .inl 10, .inl 15, .inr 7, .inr 26, .inr 44, .inr 36],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 11, .inl 13, .inr 60, .inr 56, .inr 4, .inr 6, .inl 9, .inl 15, .inl 10, .inl 12, .inr 36, .inr 7, .inr 26, .inr 8],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inl 13, .inr 2, .inl 14, .inr 64, .inl 9, .inr 0, .inl 10, .inr 43, .inl 12, .inr 3, .inl 15, .inr 4],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inr 64, .inl 13, .inr 26, .inl 14, .inl 9, .inr 0, .inl 10, .inr 43, .inr 4, .inl 12, .inr 5, .inl 15],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inl 14, .inr 52, .inl 13, .inr 2, .inl 9, .inr 0, .inl 10, .inr 43, .inl 15, .inr 29, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inl 11, .inr 42, .inr 36, .inl 14, .inr 52, .inl 13, .inl 9, .inr 0, .inl 10, .inr 43, .inr 63, .inl 15, .inr 29, .inl 12]]

private theorem check10 : ∀ y z : Fin 16,
    Check ![8, 10, y, z] (choice10 y z) := by decide +kernel

private def choice11 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 15, .inl 11, .inr 5, .inr 6, .inr 57, .inr 60, .inl 9, .inl 13, .inl 14, .inl 10, .inr 26, .inr 8, .inr 8, .inr 36],
    ![.inl 8, .inl 15, .inl 12, .inl 11, .inr 66, .inr 7, .inr 6, .inr 5, .inl 9, .inl 14, .inl 13, .inl 10, .inr 36, .inr 8, .inr 8, .inr 26],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 44, .inr 42, .inl 11, .inl 12, .inr 3, .inr 63, .inl 15, .inl 9, .inr 35, .inr 43, .inl 10, .inl 13, .inr 2, .inr 62, .inl 14],
    ![.inl 8, .inr 1, .inr 64, .inl 11, .inr 3, .inl 12, .inl 15, .inr 63, .inl 9, .inr 0, .inr 4, .inl 10, .inr 2, .inl 13, .inl 14, .inr 5],
    ![.inl 8, .inr 1, .inr 44, .inl 11, .inr 63, .inl 15, .inl 12, .inr 3, .inl 9, .inr 0, .inr 75, .inl 10, .inr 62, .inl 14, .inl 13, .inr 2],
    ![.inl 8, .inr 64, .inr 42, .inl 11, .inl 15, .inr 63, .inr 3, .inl 12, .inl 9, .inr 4, .inr 43, .inl 10, .inl 14, .inr 6, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 14, .inl 11, .inr 6, .inr 5, .inr 60, .inr 17, .inl 9, .inl 12, .inl 15, .inl 10, .inr 7, .inr 26, .inr 36, .inr 8],
    ![.inl 8, .inl 14, .inl 13, .inl 11, .inr 56, .inr 60, .inr 5, .inr 6, .inl 9, .inl 15, .inl 12, .inl 10, .inr 7, .inr 36, .inr 26, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 1, .inr 64, .inl 11, .inl 13, .inr 2, .inr 26, .inl 14, .inl 9, .inr 0, .inr 4, .inl 10, .inl 12, .inr 3, .inr 5, .inl 15],
    ![.inl 8, .inr 44, .inr 42, .inl 11, .inr 2, .inl 13, .inl 14, .inr 62, .inl 9, .inr 49, .inr 43, .inl 10, .inr 3, .inl 12, .inl 15, .inr 63],
    ![.inl 8, .inr 64, .inr 42, .inl 11, .inr 62, .inl 14, .inl 13, .inr 2, .inl 9, .inr 4, .inr 43, .inl 10, .inr 63, .inl 15, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inr 44, .inl 11, .inl 14, .inr 36, .inr 2, .inl 13, .inl 9, .inr 0, .inr 75, .inl 10, .inl 15, .inr 63, .inr 3, .inl 12]]

private theorem check11 : ∀ y z : Fin 16,
    Check ![8, 11, y, z] (choice11 y z) := by decide +kernel

private def choice12 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 17, .inr 8, .inl 11, .inl 15, .inr 48, .inr 10, .inl 9, .inl 13, .inr 68, .inr 31, .inl 10, .inl 14, .inr 23, .inr 40],
    ![.inl 8, .inr 1, .inl 12, .inr 39, .inl 11, .inr 42, .inl 15, .inr 63, .inl 9, .inr 0, .inl 13, .inr 30, .inl 10, .inr 43, .inl 14, .inr 5],
    ![.inl 8, .inr 64, .inr 3, .inl 12, .inl 11, .inr 42, .inr 63, .inl 15, .inl 9, .inr 4, .inr 2, .inl 13, .inl 10, .inr 43, .inr 4, .inl 14],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 7, .inr 66, .inl 11, .inl 12, .inr 6, .inr 4, .inl 9, .inl 14, .inr 10, .inr 36, .inl 10, .inl 13, .inr 8, .inr 26],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inl 11, .inr 42, .inl 12, .inr 3, .inl 9, .inr 0, .inl 14, .inr 27, .inl 10, .inr 43, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inl 11, .inr 42, .inr 3, .inl 12, .inl 9, .inr 0, .inr 62, .inl 14, .inl 10, .inr 43, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 33, .inr 10, .inl 11, .inl 14, .inr 8, .inr 19, .inl 9, .inl 12, .inr 40, .inr 69, .inl 10, .inl 15, .inr 31, .inr 17],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inl 11, .inr 42, .inl 14, .inr 66, .inl 9, .inr 0, .inl 12, .inr 3, .inl 10, .inr 43, .inl 15, .inr 75],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inl 11, .inr 44, .inr 26, .inl 14, .inl 9, .inr 0, .inr 3, .inl 12, .inl 10, .inr 34, .inr 5, .inl 15],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 60, .inr 56, .inl 11, .inl 13, .inr 5, .inr 6, .inl 9, .inl 15, .inr 36, .inr 7, .inl 10, .inl 12, .inr 26, .inr 8],
    ![.inl 8, .inr 1, .inl 14, .inr 62, .inl 11, .inr 42, .inl 13, .inr 2, .inl 9, .inr 0, .inl 15, .inr 63, .inl 10, .inr 43, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inr 36, .inl 14, .inl 11, .inr 42, .inr 2, .inl 13, .inl 9, .inr 0, .inr 63, .inl 15, .inl 10, .inr 43, .inr 3, .inl 12]]

private theorem check12 : ∀ y z : Fin 16,
    Check ![8, 12, y, z] (choice12 y z) := by decide +kernel

private def choice13 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 33, .inr 10, .inl 15, .inl 11, .inr 19, .inr 8, .inl 9, .inl 13, .inr 40, .inr 69, .inl 14, .inl 10, .inr 49, .inr 31],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inr 42, .inl 11, .inr 9, .inl 15, .inl 9, .inr 0, .inl 13, .inr 2, .inr 43, .inl 10, .inr 77, .inl 14],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inr 44, .inl 11, .inl 15, .inr 63, .inl 9, .inr 0, .inr 2, .inl 13, .inr 30, .inl 10, .inl 14, .inr 5],
    ![.inl 8, .inl 15, .inr 66, .inr 7, .inl 12, .inl 11, .inr 6, .inr 5, .inl 9, .inl 14, .inr 36, .inr 44, .inl 13, .inl 10, .inr 8, .inr 26],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inr 42, .inl 11, .inl 12, .inr 3, .inl 9, .inr 0, .inr 62, .inl 14, .inr 43, .inl 10, .inl 13, .inr 2],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inr 42, .inl 11, .inr 3, .inl 12, .inl 9, .inr 0, .inl 14, .inr 27, .inr 43, .inl 10, .inr 2, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 24, .inr 8, .inl 14, .inl 11, .inr 10, .inr 48, .inl 9, .inl 12, .inr 17, .inr 31, .inl 15, .inl 10, .inr 40, .inr 23],
    ![.inl 8, .inr 1, .inl 13, .inr 35, .inr 42, .inl 11, .inr 26, .inl 14, .inl 9, .inr 0, .inl 12, .inr 34, .inr 43, .inl 10, .inr 5, .inl 15],
    ![.inl 8, .inr 64, .inr 2, .inl 13, .inr 42, .inl 11, .inl 14, .inr 62, .inl 9, .inr 4, .inr 3, .inl 12, .inr 43, .inl 10, .inl 15, .inr 4],
    ![.inl 8, .inl 14, .inr 56, .inr 60, .inl 13, .inl 11, .inr 4, .inr 6, .inl 9, .inl 15, .inr 7, .inr 36, .inl 12, .inl 10, .inr 26, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 1, .inr 62, .inl 14, .inr 42, .inl 11, .inl 13, .inr 2, .inl 9, .inr 0, .inr 63, .inl 15, .inr 43, .inl 10, .inl 12, .inr 3],
    ![.inl 8, .inr 1, .inl 14, .inr 36, .inr 42, .inl 11, .inr 2, .inl 13, .inl 9, .inr 0, .inl 15, .inr 63, .inr 43, .inl 10, .inr 3, .inl 12]]

private theorem check13 : ∀ y z : Fin 16,
    Check ![8, 13, y, z] (choice13 y z) := by decide +kernel

private def choice14 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 60, .inr 57, .inr 5, .inr 6, .inl 11, .inl 15, .inl 9, .inl 13, .inr 36, .inr 44, .inr 26, .inr 8, .inl 10, .inl 14],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inl 15, .inr 63, .inl 11, .inr 42, .inl 9, .inr 0, .inl 13, .inr 2, .inl 14, .inr 6, .inl 10, .inr 43],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inr 63, .inl 15, .inl 11, .inr 42, .inl 9, .inr 0, .inr 2, .inl 13, .inr 62, .inl 14, .inl 10, .inr 43],
    ![.inl 8, .inr 1, .inl 15, .inr 63, .inl 12, .inr 9, .inl 11, .inr 42, .inl 9, .inr 0, .inl 14, .inr 27, .inl 13, .inr 35, .inl 10, .inr 43],
    ![.inl 8, .inr 1, .inr 63, .inl 15, .inr 3, .inl 12, .inl 11, .inr 44, .inl 9, .inr 0, .inr 62, .inl 14, .inr 2, .inl 13, .inl 10, .inr 27],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 33, .inr 10, .inr 8, .inr 19, .inl 11, .inl 12, .inl 9, .inl 14, .inr 40, .inr 69, .inr 31, .inr 49, .inl 10, .inl 13],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 23, .inr 60, .inr 6, .inr 4, .inl 11, .inl 14, .inl 9, .inl 12, .inr 10, .inr 36, .inr 7, .inr 26, .inl 10, .inl 15],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inl 14, .inr 62, .inl 11, .inr 42, .inl 9, .inr 0, .inl 12, .inr 3, .inl 15, .inr 63, .inl 10, .inr 43],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inr 62, .inl 14, .inl 11, .inr 42, .inl 9, .inr 0, .inr 3, .inl 12, .inr 63, .inl 15, .inl 10, .inr 43],
    ![.inl 8, .inr 1, .inl 14, .inr 74, .inl 13, .inr 2, .inl 11, .inr 42, .inl 9, .inr 0, .inl 15, .inr 28, .inl 12, .inr 3, .inl 10, .inr 43],
    ![.inl 8, .inr 64, .inr 62, .inl 14, .inr 2, .inl 13, .inl 11, .inr 42, .inl 9, .inr 4, .inr 63, .inl 15, .inr 3, .inl 12, .inl 10, .inr 43],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 24, .inr 8, .inr 48, .inr 10, .inl 11, .inl 13, .inl 9, .inl 15, .inr 16, .inr 31, .inr 17, .inr 40, .inl 10, .inl 12]]

private theorem check14 : ∀ y z : Fin 16,
    Check ![8, 14, y, z] (choice14 y z) := by decide +kernel

private def choice15 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 57, .inr 60, .inr 4, .inr 6, .inl 15, .inl 11, .inl 9, .inl 13, .inr 10, .inr 36, .inr 26, .inr 8, .inl 14, .inl 10],
    ![.inl 8, .inr 1, .inl 12, .inr 3, .inr 63, .inl 15, .inr 42, .inl 11, .inl 9, .inr 0, .inl 13, .inr 2, .inr 7, .inl 14, .inr 43, .inl 10],
    ![.inl 8, .inr 1, .inr 3, .inl 12, .inl 15, .inr 63, .inr 42, .inl 11, .inl 9, .inr 0, .inr 2, .inl 13, .inl 14, .inr 6, .inr 43, .inl 10],
    ![.inl 8, .inr 64, .inr 63, .inl 15, .inl 12, .inr 3, .inr 42, .inl 11, .inl 9, .inr 4, .inr 7, .inl 14, .inl 13, .inr 4, .inr 43, .inl 10],
    ![.inl 8, .inr 1, .inl 15, .inr 72, .inr 3, .inl 12, .inr 42, .inl 11, .inl 9, .inr 0, .inl 14, .inr 27, .inr 2, .inl 13, .inr 43, .inl 10],
    ![.inl 8, .inl 15, .inr 32, .inr 8, .inr 10, .inr 17, .inl 12, .inl 11, .inl 9, .inl 14, .inr 68, .inr 31, .inr 40, .inr 23, .inl 13, .inl 10],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 60, .inr 73, .inr 6, .inr 5, .inl 14, .inl 11, .inl 9, .inl 12, .inr 36, .inr 44, .inr 7, .inr 26, .inl 15, .inl 10],
    ![.inl 8, .inr 1, .inl 13, .inr 2, .inr 7, .inl 14, .inr 42, .inl 11, .inl 9, .inr 0, .inl 12, .inr 3, .inr 63, .inl 15, .inr 43, .inl 10],
    ![.inl 8, .inr 1, .inr 2, .inl 13, .inl 14, .inr 7, .inr 42, .inl 11, .inl 9, .inr 0, .inr 3, .inl 12, .inl 15, .inr 63, .inr 43, .inl 10],
    ![.inl 8, .inr 1, .inr 7, .inl 14, .inl 13, .inr 2, .inr 74, .inl 11, .inl 9, .inr 0, .inr 63, .inl 15, .inl 12, .inr 3, .inr 28, .inl 10],
    ![.inl 8, .inr 1, .inl 14, .inr 7, .inr 35, .inl 13, .inr 42, .inl 11, .inl 9, .inr 0, .inl 15, .inr 63, .inr 75, .inl 12, .inr 43, .inl 10],
    ![.inl 8, .inl 14, .inr 33, .inr 10, .inr 19, .inr 8, .inl 13, .inl 11, .inl 9, .inl 15, .inr 40, .inr 17, .inr 49, .inr 31, .inl 12, .inl 10],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6]]

private theorem check15 : ∀ y z : Fin 16,
    Check ![8, 15, y, z] (choice15 y z) := by decide +kernel

/-- All 4096 tuples with first column 8, including their singular cases. -/
public theorem witnessRep8 (x y z : Fin 16)
    (hinj : ∀ i : Fin 16, act ![8, x, y, z] i = 0 → i = 0) :
    ∃ w : List (Fin 4), (evalMat ![8, x, y, z] w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat ![8, x, y, z] w ≠ localTable j := by
  fin_cases x
  · exact checked_witness _ _ (check0 y z) hinj
  · exact checked_witness _ _ (check1 y z) hinj
  · exact checked_witness _ _ (check2 y z) hinj
  · exact checked_witness _ _ (check3 y z) hinj
  · exact checked_witness _ _ (check4 y z) hinj
  · exact checked_witness _ _ (check5 y z) hinj
  · exact checked_witness _ _ (check6 y z) hinj
  · exact checked_witness _ _ (check7 y z) hinj
  · exact checked_witness _ _ (check8 y z) hinj
  · exact checked_witness _ _ (check9 y z) hinj
  · exact checked_witness _ _ (check10 y z) hinj
  · exact checked_witness _ _ (check11 y z) hinj
  · exact checked_witness _ _ (check12 y z) hinj
  · exact checked_witness _ _ (check13 y z) hinj
  · exact checked_witness _ _ (check14 y z) hinj
  · exact checked_witness _ _ (check15 y z) hinj

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity
