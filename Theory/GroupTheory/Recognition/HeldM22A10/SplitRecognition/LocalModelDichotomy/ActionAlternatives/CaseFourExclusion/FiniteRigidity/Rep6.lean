module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Witnesses

/-!
# Case IV certificates with first column 6

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
    Check ![6, 0, y, z] (choice0 y z) := by decide +kernel

private def choice1 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 10, .inl 12, .inl 14, .inl 13, .inl 15, .inl 9, .inl 11, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27],
    ![.inl 8, .inl 10, .inl 14, .inl 12, .inl 15, .inl 13, .inl 9, .inl 11, .inr 5, .inr 4, .inr 4, .inr 5, .inr 5, .inr 4, .inr 4, .inr 5],
    ![.inl 8, .inl 10, .inl 13, .inl 15, .inl 12, .inl 14, .inl 9, .inl 11, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 8, .inl 10, .inl 15, .inl 13, .inl 14, .inl 12, .inl 9, .inl 11, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 10, .inr 9, .inr 37, .inr 8, .inr 12, .inl 9, .inl 11, .inl 12, .inl 14, .inr 23, .inr 50, .inr 32, .inr 40, .inl 13, .inl 15],
    ![.inl 8, .inl 10, .inr 8, .inr 12, .inr 9, .inr 37, .inl 9, .inl 11, .inl 14, .inl 12, .inr 40, .inr 32, .inr 50, .inr 23, .inl 15, .inl 13],
    ![.inl 8, .inl 10, .inr 37, .inr 9, .inr 12, .inr 8, .inl 9, .inl 11, .inr 51, .inr 24, .inl 12, .inl 14, .inl 13, .inl 15, .inr 40, .inr 38],
    ![.inl 8, .inl 10, .inr 12, .inr 8, .inr 37, .inr 9, .inl 9, .inl 11, .inr 38, .inr 40, .inl 14, .inl 12, .inl 15, .inl 13, .inr 24, .inr 51],
    ![.inl 8, .inl 10, .inr 23, .inr 50, .inr 32, .inr 40, .inl 9, .inl 11, .inr 8, .inr 12, .inl 13, .inl 15, .inl 12, .inl 14, .inr 9, .inr 19],
    ![.inl 8, .inl 10, .inr 32, .inr 40, .inr 23, .inr 50, .inl 9, .inl 11, .inr 19, .inr 9, .inl 15, .inl 13, .inl 14, .inl 12, .inr 12, .inr 8],
    ![.inl 8, .inl 10, .inr 51, .inr 24, .inr 40, .inr 38, .inl 9, .inl 11, .inl 13, .inl 15, .inr 12, .inr 8, .inr 19, .inr 9, .inl 12, .inl 14],
    ![.inl 8, .inl 10, .inr 40, .inr 38, .inr 51, .inr 24, .inl 9, .inl 11, .inl 15, .inl 13, .inr 9, .inr 19, .inr 8, .inr 12, .inl 14, .inl 12]]

private theorem check1 : ∀ y z : Fin 16,
    Check ![6, 1, y, z] (choice1 y z) := by decide +kernel

private def choice2 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 10, .inl 14, .inl 11, .inl 15, .inl 9, .inl 13, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 10, .inl 12, .inl 11, .inl 13, .inl 9, .inl 15, .inr 0, .inr 1, .inr 0, .inr 1, .inr 1, .inr 0, .inr 1, .inr 0],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 10, .inl 13, .inl 11, .inl 12, .inl 9, .inl 14, .inr 3, .inr 43, .inr 3, .inr 43, .inr 43, .inr 3, .inr 43, .inr 3],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 10, .inl 15, .inl 11, .inl 14, .inl 9, .inl 12, .inr 5, .inr 4, .inr 4, .inr 5, .inr 5, .inr 4, .inr 4, .inr 5],
    ![.inl 8, .inr 6, .inl 10, .inr 26, .inl 11, .inr 5, .inl 9, .inr 29, .inl 12, .inr 36, .inl 14, .inr 28, .inl 15, .inr 27, .inl 13, .inr 52],
    ![.inl 8, .inr 29, .inl 10, .inr 5, .inl 11, .inr 26, .inl 9, .inr 6, .inr 52, .inl 12, .inr 27, .inl 14, .inr 28, .inl 15, .inr 36, .inl 13],
    ![.inl 8, .inr 26, .inl 10, .inr 6, .inl 11, .inr 29, .inl 9, .inr 5, .inl 14, .inr 36, .inl 12, .inr 27, .inl 13, .inr 28, .inl 15, .inr 52],
    ![.inl 8, .inr 5, .inl 10, .inr 29, .inl 11, .inr 6, .inl 9, .inr 26, .inr 52, .inl 14, .inr 28, .inl 12, .inr 27, .inl 13, .inr 36, .inl 15],
    ![.inl 8, .inr 36, .inl 10, .inr 28, .inl 11, .inr 27, .inl 9, .inr 52, .inl 15, .inr 5, .inl 13, .inr 6, .inl 12, .inr 29, .inl 14, .inr 26],
    ![.inl 8, .inr 52, .inl 10, .inr 27, .inl 11, .inr 28, .inl 9, .inr 36, .inr 26, .inl 15, .inr 29, .inl 13, .inr 6, .inl 12, .inr 5, .inl 14],
    ![.inl 8, .inr 27, .inl 10, .inr 36, .inl 11, .inr 52, .inl 9, .inr 28, .inl 13, .inr 5, .inl 15, .inr 6, .inl 14, .inr 29, .inl 12, .inr 26],
    ![.inl 8, .inr 28, .inl 10, .inr 52, .inl 11, .inr 36, .inl 9, .inr 27, .inr 26, .inl 13, .inr 29, .inl 15, .inr 6, .inl 14, .inr 5, .inl 12]]

private theorem check2 : ∀ y z : Fin 16,
    Check ![6, 2, y, z] (choice2 y z) := by decide +kernel

private def choice3 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 14, .inl 10, .inl 15, .inl 11, .inl 9, .inl 13, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36],
    ![.inl 8, .inl 14, .inl 12, .inl 10, .inl 13, .inl 11, .inl 9, .inl 15, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 15, .inl 13, .inl 10, .inl 12, .inl 11, .inl 9, .inl 14, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 15, .inl 10, .inl 14, .inl 11, .inl 9, .inl 12, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 8, .inr 29, .inr 5, .inl 10, .inr 4, .inl 11, .inl 9, .inr 6, .inl 12, .inr 52, .inr 27, .inl 14, .inr 28, .inl 15, .inl 13, .inr 36],
    ![.inl 8, .inr 6, .inr 4, .inl 10, .inr 5, .inl 11, .inl 9, .inr 29, .inr 36, .inl 12, .inl 14, .inr 28, .inl 15, .inr 27, .inr 52, .inl 13],
    ![.inl 8, .inr 5, .inr 29, .inl 10, .inr 6, .inl 11, .inl 9, .inr 4, .inr 52, .inl 14, .inl 12, .inr 28, .inl 13, .inr 27, .inr 36, .inl 15],
    ![.inl 8, .inr 4, .inr 6, .inl 10, .inr 29, .inl 11, .inl 9, .inr 5, .inl 14, .inr 36, .inr 27, .inl 12, .inr 28, .inl 13, .inl 15, .inr 52],
    ![.inl 8, .inr 52, .inr 27, .inl 10, .inr 28, .inl 11, .inl 9, .inr 36, .inr 4, .inl 15, .inl 13, .inr 29, .inl 12, .inr 6, .inr 5, .inl 14],
    ![.inl 8, .inr 36, .inr 28, .inl 10, .inr 27, .inl 11, .inl 9, .inr 52, .inl 15, .inr 5, .inr 6, .inl 13, .inr 29, .inl 12, .inl 14, .inr 4],
    ![.inl 8, .inr 28, .inr 52, .inl 10, .inr 36, .inl 11, .inl 9, .inr 27, .inl 13, .inr 4, .inr 29, .inl 15, .inr 6, .inl 14, .inl 12, .inr 5],
    ![.inl 8, .inr 27, .inr 36, .inl 10, .inr 52, .inl 11, .inl 9, .inr 28, .inr 5, .inl 13, .inl 15, .inr 6, .inl 14, .inr 29, .inr 4, .inl 12]]

private theorem check3 : ∀ y z : Fin 16,
    Check ![6, 3, y, z] (choice3 y z) := by decide +kernel

private def choice4 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 11, .inl 15, .inl 10, .inl 14, .inl 9, .inl 13, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 11, .inl 12, .inl 10, .inl 13, .inl 9, .inl 14, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43, .inr 43],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 11, .inl 13, .inl 10, .inl 12, .inl 9, .inl 15, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 11, .inl 14, .inl 10, .inl 15, .inl 9, .inl 12, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36],
    ![.inl 8, .inr 27, .inl 11, .inr 52, .inl 10, .inr 36, .inl 9, .inr 28, .inl 12, .inr 4, .inl 15, .inr 6, .inl 14, .inr 29, .inl 13, .inr 5],
    ![.inl 8, .inr 28, .inl 11, .inr 36, .inl 10, .inr 52, .inl 9, .inr 27, .inr 5, .inl 12, .inr 29, .inl 15, .inr 6, .inl 14, .inr 4, .inl 13],
    ![.inl 8, .inr 36, .inl 11, .inr 27, .inl 10, .inr 28, .inl 9, .inr 52, .inl 15, .inr 5, .inl 12, .inr 29, .inl 13, .inr 6, .inl 14, .inr 4],
    ![.inl 8, .inr 52, .inl 11, .inr 28, .inl 10, .inr 27, .inl 9, .inr 36, .inr 4, .inl 15, .inr 6, .inl 12, .inr 29, .inl 13, .inr 5, .inl 14],
    ![.inl 8, .inr 4, .inl 11, .inr 29, .inl 10, .inr 6, .inl 9, .inr 5, .inl 14, .inr 36, .inl 13, .inr 28, .inl 12, .inr 27, .inl 15, .inr 52],
    ![.inl 8, .inr 5, .inl 11, .inr 6, .inl 10, .inr 29, .inl 9, .inr 4, .inr 52, .inl 14, .inr 27, .inl 13, .inr 28, .inl 12, .inr 36, .inl 15],
    ![.inl 8, .inr 6, .inl 11, .inr 5, .inl 10, .inr 4, .inl 9, .inr 29, .inl 13, .inr 52, .inl 14, .inr 28, .inl 15, .inr 27, .inl 12, .inr 36],
    ![.inl 8, .inr 29, .inl 11, .inr 4, .inl 10, .inr 5, .inl 9, .inr 6, .inr 36, .inl 13, .inr 27, .inl 14, .inr 28, .inl 15, .inr 52, .inl 12]]

private theorem check4 : ∀ y z : Fin 16,
    Check ![6, 4, y, z] (choice4 y z) := by decide +kernel

private def choice5 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 15, .inl 11, .inl 14, .inl 10, .inl 9, .inl 13, .inr 5, .inr 4, .inr 5, .inr 4, .inr 4, .inr 5, .inr 4, .inr 5],
    ![.inl 8, .inl 15, .inl 12, .inl 11, .inl 13, .inl 10, .inl 9, .inl 14, .inr 43, .inr 3, .inr 3, .inr 43, .inr 43, .inr 3, .inr 3, .inr 43],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 14, .inl 13, .inl 11, .inl 12, .inl 10, .inl 9, .inl 15, .inr 0, .inr 1, .inr 1, .inr 0, .inr 0, .inr 1, .inr 1, .inr 0],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 14, .inl 11, .inl 15, .inl 10, .inl 9, .inl 12, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 8, .inr 28, .inr 36, .inl 11, .inr 52, .inl 10, .inl 9, .inr 27, .inl 12, .inr 5, .inr 29, .inl 15, .inr 6, .inl 14, .inl 13, .inr 26],
    ![.inl 8, .inr 27, .inr 52, .inl 11, .inr 36, .inl 10, .inl 9, .inr 28, .inr 26, .inl 12, .inl 15, .inr 6, .inl 14, .inr 29, .inr 5, .inl 13],
    ![.inl 8, .inr 52, .inr 28, .inl 11, .inr 27, .inl 10, .inl 9, .inr 36, .inr 26, .inl 15, .inl 12, .inr 6, .inl 13, .inr 29, .inr 5, .inl 14],
    ![.inl 8, .inr 36, .inr 27, .inl 11, .inr 28, .inl 10, .inl 9, .inr 52, .inl 15, .inr 5, .inr 29, .inl 12, .inr 6, .inl 13, .inl 14, .inr 26],
    ![.inl 8, .inr 5, .inr 6, .inl 11, .inr 29, .inl 10, .inl 9, .inr 26, .inr 52, .inl 14, .inl 13, .inr 27, .inl 12, .inr 28, .inr 36, .inl 15],
    ![.inl 8, .inr 26, .inr 29, .inl 11, .inr 6, .inl 10, .inl 9, .inr 5, .inl 14, .inr 36, .inr 28, .inl 13, .inr 27, .inl 12, .inl 15, .inr 52],
    ![.inl 8, .inr 29, .inr 26, .inl 11, .inr 5, .inl 10, .inl 9, .inr 6, .inl 13, .inr 36, .inr 27, .inl 14, .inr 28, .inl 15, .inl 12, .inr 52],
    ![.inl 8, .inr 6, .inr 5, .inl 11, .inr 26, .inl 10, .inl 9, .inr 29, .inr 52, .inl 13, .inl 14, .inr 28, .inl 15, .inr 27, .inr 36, .inl 12]]

private theorem check5 : ∀ y z : Fin 16,
    Check ![6, 5, y, z] (choice5 y z) := by decide +kernel

private def choice6 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
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

private theorem check6 : ∀ y z : Fin 16,
    Check ![6, 6, y, z] (choice6 y z) := by decide +kernel

private def choice7 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 11, .inl 12, .inl 15, .inl 13, .inl 14, .inl 9, .inl 10, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36, .inr 36],
    ![.inl 8, .inl 11, .inl 15, .inl 12, .inl 14, .inl 13, .inl 9, .inl 10, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 8, .inl 11, .inl 13, .inl 14, .inl 12, .inl 15, .inl 9, .inl 10, .inr 5, .inr 4, .inr 5, .inr 4, .inr 4, .inr 5, .inr 4, .inr 5],
    ![.inl 8, .inl 11, .inl 14, .inl 13, .inl 15, .inl 12, .inl 9, .inl 10, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27, .inr 27],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 11, .inr 23, .inr 50, .inr 32, .inr 40, .inl 9, .inl 10, .inl 12, .inl 15, .inr 8, .inr 12, .inr 9, .inr 37, .inl 13, .inl 14],
    ![.inl 8, .inl 11, .inr 32, .inr 40, .inr 23, .inr 50, .inl 9, .inl 10, .inl 15, .inl 12, .inr 37, .inr 9, .inr 12, .inr 8, .inl 14, .inl 13],
    ![.inl 8, .inl 11, .inr 40, .inr 38, .inr 51, .inr 24, .inl 9, .inl 10, .inr 37, .inr 9, .inl 12, .inl 15, .inl 13, .inl 14, .inr 12, .inr 8],
    ![.inl 8, .inl 11, .inr 51, .inr 24, .inr 40, .inr 38, .inl 9, .inl 10, .inr 8, .inr 12, .inl 15, .inl 12, .inl 14, .inl 13, .inr 9, .inr 37],
    ![.inl 8, .inl 11, .inr 8, .inr 12, .inr 9, .inr 19, .inl 9, .inl 10, .inr 32, .inr 40, .inl 13, .inl 14, .inl 12, .inl 15, .inr 23, .inr 50],
    ![.inl 8, .inl 11, .inr 9, .inr 19, .inr 8, .inr 12, .inl 9, .inl 10, .inr 50, .inr 23, .inl 14, .inl 13, .inl 15, .inl 12, .inr 40, .inr 32],
    ![.inl 8, .inl 11, .inr 19, .inr 9, .inr 12, .inr 8, .inl 9, .inl 10, .inl 13, .inl 14, .inr 51, .inr 24, .inr 40, .inr 38, .inl 12, .inl 15],
    ![.inl 8, .inl 11, .inr 12, .inr 8, .inr 19, .inr 9, .inl 9, .inl 10, .inl 14, .inl 13, .inr 38, .inr 40, .inr 24, .inr 51, .inl 15, .inl 12]]

private theorem check7 : ∀ y z : Fin 16,
    Check ![6, 7, y, z] (choice7 y z) := by decide +kernel

private def choice8 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 8, .inr 10, .inr 9, .inr 21, .inl 9, .inl 13, .inl 10, .inl 14, .inr 47, .inr 40, .inr 23, .inr 50, .inl 11, .inl 15],
    ![.inl 8, .inr 6, .inl 12, .inr 36, .inl 13, .inr 52, .inl 9, .inr 29, .inl 10, .inr 4, .inl 14, .inr 28, .inl 15, .inr 27, .inl 11, .inr 5],
    ![.inl 8, .inr 29, .inr 52, .inl 12, .inr 36, .inl 13, .inl 9, .inr 6, .inl 10, .inr 5, .inr 27, .inl 14, .inr 28, .inl 15, .inl 11, .inr 26],
    ![.inl 8, .inr 27, .inl 13, .inr 5, .inl 12, .inr 26, .inl 9, .inr 28, .inl 10, .inr 36, .inl 15, .inr 6, .inl 14, .inr 29, .inl 11, .inr 52],
    ![.inl 8, .inr 28, .inr 4, .inl 13, .inr 5, .inl 12, .inl 9, .inr 27, .inl 10, .inr 52, .inr 29, .inl 15, .inr 6, .inl 14, .inl 11, .inr 36],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 47, .inr 40, .inr 23, .inr 50, .inl 9, .inl 12, .inl 10, .inl 15, .inr 9, .inr 21, .inr 8, .inr 10, .inl 11, .inl 14],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 0, .inr 0, .inr 1, .inr 1, .inl 9, .inl 15, .inl 10, .inl 12, .inr 1, .inr 1, .inr 1, .inr 1, .inl 11, .inl 13],
    ![.inl 8, .inr 9, .inl 14, .inr 24, .inl 15, .inr 32, .inl 9, .inr 8, .inl 10, .inr 10, .inl 12, .inr 12, .inl 13, .inr 13, .inl 11, .inr 11],
    ![.inl 8, .inr 24, .inr 9, .inl 14, .inr 8, .inl 15, .inl 9, .inr 32, .inl 10, .inr 13, .inr 11, .inl 12, .inr 10, .inl 13, .inl 11, .inr 12],
    ![.inl 8, .inr 12, .inl 15, .inr 10, .inl 14, .inr 11, .inl 9, .inr 13, .inl 10, .inr 15, .inl 13, .inr 8, .inl 12, .inr 9, .inl 11, .inr 47],
    ![.inl 8, .inr 11, .inr 13, .inl 15, .inr 12, .inl 14, .inl 9, .inr 10, .inl 10, .inr 8, .inr 15, .inl 13, .inr 47, .inl 12, .inl 11, .inr 9],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 43, .inr 43, .inl 9, .inl 14, .inl 10, .inl 13, .inr 3, .inr 3, .inr 43, .inr 43, .inl 11, .inl 12]]

private theorem check8 : ∀ y z : Fin 16,
    Check ![6, 8, y, z] (choice8 y z) := by decide +kernel

private def choice9 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 9, .inr 21, .inr 8, .inr 10, .inl 9, .inl 13, .inl 14, .inl 10, .inr 50, .inr 23, .inr 40, .inr 47, .inl 15, .inl 11],
    ![.inl 8, .inr 29, .inl 12, .inr 52, .inl 13, .inr 36, .inl 9, .inr 6, .inr 5, .inl 10, .inr 27, .inl 14, .inr 28, .inl 15, .inr 4, .inl 11],
    ![.inl 8, .inr 6, .inr 36, .inl 12, .inr 52, .inl 13, .inl 9, .inr 29, .inr 26, .inl 10, .inl 14, .inr 28, .inl 15, .inr 27, .inr 5, .inl 11],
    ![.inl 8, .inr 28, .inl 13, .inr 26, .inl 12, .inr 5, .inl 9, .inr 27, .inr 52, .inl 10, .inr 29, .inl 15, .inr 6, .inl 14, .inr 36, .inl 11],
    ![.inl 8, .inr 27, .inr 5, .inl 13, .inr 4, .inl 12, .inl 9, .inr 28, .inr 36, .inl 10, .inl 15, .inr 6, .inl 14, .inr 29, .inr 52, .inl 11],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 23, .inr 50, .inr 47, .inr 40, .inl 9, .inl 12, .inl 15, .inl 10, .inr 10, .inr 8, .inr 21, .inr 9, .inl 14, .inl 11],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 0, .inr 0, .inl 9, .inl 15, .inl 12, .inl 10, .inr 1, .inr 1, .inr 1, .inr 1, .inl 13, .inl 11],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 32, .inr 8, .inl 14, .inr 9, .inl 15, .inl 9, .inr 24, .inr 12, .inl 10, .inl 12, .inr 10, .inl 13, .inr 11, .inr 13, .inl 11],
    ![.inl 8, .inr 8, .inl 14, .inr 32, .inl 15, .inr 24, .inl 9, .inr 9, .inr 11, .inl 10, .inr 13, .inl 12, .inr 12, .inl 13, .inr 10, .inl 11],
    ![.inl 8, .inr 10, .inr 12, .inl 15, .inr 13, .inl 14, .inl 9, .inr 11, .inr 9, .inl 10, .inl 13, .inr 47, .inl 12, .inr 15, .inr 8, .inl 11],
    ![.inl 8, .inr 13, .inl 15, .inr 11, .inl 14, .inr 10, .inl 9, .inr 12, .inr 47, .inl 10, .inr 9, .inl 13, .inr 8, .inl 12, .inr 15, .inl 11],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 43, .inr 43, .inl 9, .inl 14, .inl 13, .inl 10, .inr 43, .inr 43, .inr 3, .inr 3, .inl 12, .inl 11],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7]]

private theorem check9 : ∀ y z : Fin 16,
    Check ![6, 9, y, z] (choice9 y z) := by decide +kernel

private def choice10 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 47, .inr 40, .inr 23, .inr 50, .inl 9, .inl 13, .inr 8, .inr 10, .inl 10, .inl 14, .inl 11, .inl 15, .inr 9, .inr 24],
    ![.inl 8, .inr 4, .inl 12, .inr 27, .inl 13, .inr 28, .inl 9, .inr 5, .inl 14, .inr 36, .inl 10, .inr 6, .inl 11, .inr 29, .inl 15, .inr 52],
    ![.inl 8, .inr 5, .inr 28, .inl 12, .inr 27, .inl 13, .inl 9, .inr 26, .inr 52, .inl 14, .inl 10, .inr 29, .inl 11, .inr 6, .inr 36, .inl 15],
    ![.inl 8, .inr 36, .inl 13, .inr 6, .inl 12, .inr 29, .inl 9, .inr 52, .inl 15, .inr 5, .inl 10, .inr 28, .inl 11, .inr 27, .inl 14, .inr 26],
    ![.inl 8, .inr 52, .inr 29, .inl 13, .inr 6, .inl 12, .inl 9, .inr 36, .inr 4, .inl 15, .inl 10, .inr 27, .inl 11, .inr 28, .inr 5, .inl 14],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 9, .inr 24, .inr 8, .inr 10, .inl 9, .inl 12, .inr 47, .inr 40, .inl 10, .inl 15, .inl 11, .inl 14, .inr 23, .inr 50],
    ![.inl 8, .inr 10, .inl 14, .inr 13, .inl 15, .inr 12, .inl 9, .inr 11, .inl 12, .inr 15, .inl 10, .inr 9, .inl 11, .inr 8, .inl 13, .inr 32],
    ![.inl 8, .inr 12, .inr 11, .inl 14, .inr 10, .inl 15, .inl 9, .inr 13, .inr 9, .inl 12, .inl 10, .inr 15, .inl 11, .inr 32, .inr 8, .inl 13],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1, .inl 9, .inl 15, .inr 0, .inr 0, .inl 10, .inl 12, .inl 11, .inl 13, .inr 1, .inr 1],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 42, .inr 4, .inr 43, .inr 43, .inl 9, .inl 14, .inr 43, .inr 43, .inl 10, .inl 13, .inl 11, .inl 12, .inr 43, .inr 43],
    ![.inl 8, .inr 16, .inl 15, .inr 8, .inl 14, .inr 9, .inl 9, .inr 47, .inl 13, .inr 10, .inl 10, .inr 40, .inl 11, .inr 12, .inl 12, .inr 11],
    ![.inl 8, .inr 8, .inr 16, .inl 15, .inr 47, .inl 14, .inl 9, .inr 9, .inr 12, .inl 13, .inl 10, .inr 11, .inl 11, .inr 10, .inr 40, .inl 12]]

private theorem check10 : ∀ y z : Fin 16,
    Check ![6, 10, y, z] (choice10 y z) := by decide +kernel

private def choice11 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 23, .inr 50, .inr 47, .inr 40, .inl 9, .inl 13, .inr 24, .inr 9, .inl 14, .inl 10, .inl 15, .inl 11, .inr 10, .inr 8],
    ![.inl 8, .inr 5, .inl 12, .inr 28, .inl 13, .inr 27, .inl 9, .inr 4, .inr 52, .inl 14, .inr 29, .inl 10, .inr 6, .inl 11, .inr 36, .inl 15],
    ![.inl 8, .inr 26, .inr 27, .inl 12, .inr 28, .inl 13, .inl 9, .inr 5, .inl 14, .inr 36, .inr 6, .inl 10, .inr 29, .inl 11, .inl 15, .inr 52],
    ![.inl 8, .inr 52, .inl 13, .inr 29, .inl 12, .inr 6, .inl 9, .inr 36, .inr 26, .inl 15, .inr 27, .inl 10, .inr 28, .inl 11, .inr 5, .inl 14],
    ![.inl 8, .inr 36, .inr 6, .inl 13, .inr 29, .inl 12, .inl 9, .inr 52, .inl 15, .inr 5, .inr 28, .inl 10, .inr 27, .inl 11, .inl 14, .inr 4],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 8, .inr 10, .inr 9, .inr 24, .inl 9, .inl 12, .inr 50, .inr 23, .inl 15, .inl 10, .inl 14, .inl 11, .inr 40, .inr 47],
    ![.inl 8, .inr 13, .inr 10, .inl 14, .inr 11, .inl 15, .inl 9, .inr 12, .inl 12, .inr 8, .inr 32, .inl 10, .inr 15, .inl 11, .inl 13, .inr 9],
    ![.inl 8, .inr 11, .inl 14, .inr 12, .inl 15, .inr 13, .inl 9, .inr 10, .inr 32, .inl 12, .inr 8, .inl 10, .inr 9, .inl 11, .inr 15, .inl 13],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1, .inl 9, .inl 15, .inr 1, .inr 1, .inl 12, .inl 10, .inl 13, .inl 11, .inr 0, .inr 0],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 42, .inr 4, .inl 9, .inl 14, .inr 43, .inr 43, .inl 13, .inl 10, .inl 12, .inl 11, .inr 43, .inr 43],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 9, .inr 47, .inl 15, .inr 16, .inl 14, .inl 9, .inr 8, .inl 13, .inr 40, .inr 10, .inl 10, .inr 11, .inl 11, .inl 12, .inr 12],
    ![.inl 8, .inr 47, .inl 15, .inr 9, .inl 14, .inr 8, .inl 9, .inr 16, .inr 11, .inl 13, .inr 12, .inl 10, .inr 40, .inl 11, .inr 10, .inl 12]]

private theorem check11 : ∀ y z : Fin 16,
    Check ![6, 11, y, z] (choice11 y z) := by decide +kernel

private def choice12 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 10, .inr 8, .inr 21, .inr 9, .inl 9, .inl 13, .inr 48, .inr 19, .inl 11, .inl 15, .inl 10, .inl 14, .inr 40, .inr 49],
    ![.inl 8, .inr 36, .inl 12, .inr 29, .inl 13, .inr 6, .inl 9, .inr 52, .inl 15, .inr 5, .inl 11, .inr 27, .inl 10, .inr 28, .inl 14, .inr 4],
    ![.inl 8, .inr 52, .inr 6, .inl 12, .inr 29, .inl 13, .inl 9, .inr 36, .inr 26, .inl 15, .inl 11, .inr 28, .inl 10, .inr 27, .inr 5, .inl 14],
    ![.inl 8, .inr 26, .inl 13, .inr 28, .inl 12, .inr 27, .inl 9, .inr 5, .inl 14, .inr 36, .inl 11, .inr 29, .inl 10, .inr 6, .inl 15, .inr 52],
    ![.inl 8, .inr 5, .inr 27, .inl 13, .inr 28, .inl 12, .inl 9, .inr 4, .inr 52, .inl 14, .inl 11, .inr 6, .inl 10, .inr 29, .inr 36, .inl 15],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 48, .inr 19, .inr 40, .inr 49, .inl 9, .inl 12, .inr 21, .inr 9, .inl 11, .inl 14, .inl 10, .inl 15, .inr 10, .inr 8],
    ![.inl 8, .inr 9, .inl 15, .inr 47, .inl 14, .inr 19, .inl 9, .inr 8, .inl 12, .inr 12, .inl 11, .inr 11, .inl 10, .inr 10, .inl 13, .inr 13],
    ![.inl 8, .inr 47, .inr 9, .inl 15, .inr 8, .inl 14, .inl 9, .inr 19, .inr 10, .inl 12, .inl 11, .inr 13, .inl 10, .inr 12, .inr 11, .inl 13],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 4, .inr 42, .inr 43, .inr 43, .inl 9, .inl 14, .inr 43, .inr 43, .inl 11, .inl 12, .inl 10, .inl 13, .inr 43, .inr 43],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1, .inl 9, .inl 15, .inr 1, .inr 1, .inl 11, .inl 13, .inl 10, .inl 12, .inr 0, .inr 0],
    ![.inl 8, .inr 12, .inl 14, .inr 40, .inl 15, .inr 10, .inl 9, .inr 13, .inl 13, .inr 8, .inl 11, .inr 32, .inl 10, .inr 24, .inl 12, .inr 9],
    ![.inl 8, .inr 10, .inr 13, .inl 14, .inr 12, .inl 15, .inl 9, .inr 40, .inr 32, .inl 13, .inl 11, .inr 8, .inl 10, .inr 9, .inr 24, .inl 12]]

private theorem check12 : ∀ y z : Fin 16,
    Check ![6, 12, y, z] (choice12 y z) := by decide +kernel

private def choice13 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 21, .inr 9, .inr 10, .inr 8, .inl 9, .inl 13, .inr 49, .inr 40, .inl 15, .inl 11, .inl 14, .inl 10, .inr 19, .inr 48],
    ![.inl 8, .inr 52, .inl 12, .inr 6, .inl 13, .inr 29, .inl 9, .inr 36, .inr 4, .inl 15, .inr 28, .inl 11, .inr 27, .inl 10, .inr 5, .inl 14],
    ![.inl 8, .inr 36, .inr 29, .inl 12, .inr 6, .inl 13, .inl 9, .inr 52, .inl 15, .inr 5, .inr 27, .inl 11, .inr 28, .inl 10, .inl 14, .inr 26],
    ![.inl 8, .inr 5, .inl 13, .inr 27, .inl 12, .inr 28, .inl 9, .inr 26, .inr 52, .inl 14, .inr 6, .inl 11, .inr 29, .inl 10, .inr 36, .inl 15],
    ![.inl 8, .inr 4, .inr 28, .inl 13, .inr 27, .inl 12, .inl 9, .inr 5, .inl 14, .inr 36, .inr 29, .inl 11, .inr 6, .inl 10, .inl 15, .inr 52],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 40, .inr 49, .inr 48, .inr 19, .inl 9, .inl 12, .inr 8, .inr 10, .inl 14, .inl 11, .inl 15, .inl 10, .inr 9, .inr 21],
    ![.inl 8, .inr 19, .inr 8, .inl 15, .inr 9, .inl 14, .inl 9, .inr 47, .inl 12, .inr 11, .inr 12, .inl 11, .inr 13, .inl 10, .inl 13, .inr 10],
    ![.inl 8, .inr 8, .inl 15, .inr 19, .inl 14, .inr 47, .inl 9, .inr 9, .inr 13, .inl 12, .inr 10, .inl 11, .inr 11, .inl 10, .inr 12, .inl 13],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 4, .inr 42, .inl 9, .inl 14, .inr 43, .inr 43, .inl 12, .inl 11, .inl 13, .inl 10, .inr 43, .inr 43],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1, .inl 9, .inl 15, .inr 0, .inr 0, .inl 13, .inl 11, .inl 12, .inl 10, .inr 1, .inr 1],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 40, .inr 12, .inl 14, .inr 13, .inl 15, .inl 9, .inr 10, .inl 13, .inr 24, .inr 9, .inl 11, .inr 8, .inl 10, .inl 12, .inr 32],
    ![.inl 8, .inr 13, .inl 14, .inr 10, .inl 15, .inr 40, .inl 9, .inr 12, .inr 9, .inl 13, .inr 24, .inl 11, .inr 32, .inl 10, .inr 8, .inl 12]]

private theorem check13 : ∀ y z : Fin 16,
    Check ![6, 13, y, z] (choice13 y z) := by decide +kernel

private def choice14 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 40, .inr 49, .inr 48, .inr 19, .inl 9, .inl 13, .inl 11, .inl 15, .inr 24, .inr 9, .inr 10, .inr 8, .inl 10, .inl 14],
    ![.inl 8, .inr 27, .inl 12, .inr 4, .inl 13, .inr 5, .inl 9, .inr 28, .inl 11, .inr 52, .inl 15, .inr 6, .inl 14, .inr 29, .inl 10, .inr 36],
    ![.inl 8, .inr 28, .inr 5, .inl 12, .inr 26, .inl 13, .inl 9, .inr 27, .inl 11, .inr 36, .inr 29, .inl 15, .inr 6, .inl 14, .inl 10, .inr 52],
    ![.inl 8, .inr 6, .inl 13, .inr 52, .inl 12, .inr 36, .inl 9, .inr 29, .inl 11, .inr 5, .inl 14, .inr 28, .inl 15, .inr 27, .inl 10, .inr 26],
    ![.inl 8, .inr 29, .inr 36, .inl 13, .inr 52, .inl 12, .inl 9, .inr 6, .inl 11, .inr 4, .inr 27, .inl 14, .inr 28, .inl 15, .inl 10, .inr 5],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 10, .inr 8, .inr 24, .inr 9, .inl 9, .inl 12, .inl 11, .inl 14, .inr 40, .inr 49, .inr 48, .inr 19, .inl 10, .inl 15],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 43, .inr 43, .inl 9, .inl 14, .inl 11, .inl 12, .inr 43, .inr 43, .inr 3, .inr 3, .inl 10, .inl 13],
    ![.inl 8, .inr 10, .inl 15, .inr 12, .inl 14, .inr 40, .inl 9, .inr 11, .inl 11, .inr 8, .inl 12, .inr 19, .inl 13, .inr 47, .inl 10, .inr 9],
    ![.inl 8, .inr 40, .inr 11, .inl 15, .inr 10, .inl 14, .inl 9, .inr 12, .inl 11, .inr 19, .inr 8, .inl 12, .inr 9, .inl 13, .inl 10, .inr 47],
    ![.inl 8, .inr 38, .inl 14, .inr 9, .inl 15, .inr 8, .inl 9, .inr 32, .inl 11, .inr 12, .inl 13, .inr 10, .inl 12, .inr 40, .inl 10, .inr 13],
    ![.inl 8, .inr 9, .inr 38, .inl 14, .inr 32, .inl 15, .inl 9, .inr 8, .inl 11, .inr 40, .inr 13, .inl 13, .inr 12, .inl 12, .inl 10, .inr 10],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inr 0, .inr 0, .inr 1, .inr 1, .inl 9, .inl 15, .inl 11, .inl 13, .inr 1, .inr 1, .inr 1, .inr 1, .inl 10, .inl 12]]

private theorem check14 : ∀ y z : Fin 16,
    Check ![6, 14, y, z] (choice14 y z) := by decide +kernel

private def choice15 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inr 48, .inr 19, .inr 40, .inr 49, .inl 9, .inl 13, .inl 15, .inl 11, .inr 8, .inr 10, .inr 9, .inr 24, .inl 14, .inl 10],
    ![.inl 8, .inr 28, .inl 12, .inr 5, .inl 13, .inr 4, .inl 9, .inr 27, .inr 36, .inl 11, .inr 29, .inl 15, .inr 6, .inl 14, .inr 52, .inl 10],
    ![.inl 8, .inr 27, .inr 26, .inl 12, .inr 5, .inl 13, .inl 9, .inr 28, .inr 52, .inl 11, .inl 15, .inr 6, .inl 14, .inr 29, .inr 36, .inl 10],
    ![.inl 8, .inr 29, .inl 13, .inr 36, .inl 12, .inr 52, .inl 9, .inr 6, .inr 26, .inl 11, .inr 27, .inl 14, .inr 28, .inl 15, .inr 5, .inl 10],
    ![.inl 8, .inr 6, .inr 52, .inl 13, .inr 36, .inl 12, .inl 9, .inr 29, .inr 5, .inl 11, .inl 14, .inr 28, .inl 15, .inr 27, .inr 4, .inl 10],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inr 24, .inr 9, .inr 10, .inr 8, .inl 9, .inl 12, .inl 14, .inl 11, .inr 19, .inr 48, .inr 49, .inr 40, .inl 15, .inl 10],
    ![.inl 8, .inl 15, .inr 43, .inr 43, .inr 43, .inr 43, .inl 9, .inl 14, .inl 12, .inl 11, .inr 3, .inr 3, .inr 43, .inr 43, .inl 13, .inl 10],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 12, .inr 10, .inl 15, .inr 11, .inl 14, .inl 9, .inr 40, .inr 47, .inl 11, .inl 12, .inr 9, .inl 13, .inr 8, .inr 19, .inl 10],
    ![.inl 8, .inr 11, .inl 15, .inr 40, .inl 14, .inr 12, .inl 9, .inr 10, .inr 9, .inl 11, .inr 47, .inl 12, .inr 19, .inl 13, .inr 8, .inl 10],
    ![.inl 8, .inr 8, .inr 32, .inl 14, .inr 38, .inl 15, .inl 9, .inr 9, .inr 10, .inl 11, .inl 13, .inr 12, .inl 12, .inr 13, .inr 40, .inl 10],
    ![.inl 8, .inr 32, .inl 14, .inr 8, .inl 15, .inr 9, .inl 9, .inr 38, .inr 13, .inl 11, .inr 40, .inl 13, .inr 10, .inl 12, .inr 12, .inl 10],
    ![.inl 8, .inl 14, .inr 1, .inr 1, .inr 0, .inr 0, .inl 9, .inl 15, .inl 13, .inl 11, .inr 1, .inr 1, .inr 1, .inr 1, .inl 12, .inl 10],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6]]

private theorem check15 : ∀ y z : Fin 16,
    Check ![6, 15, y, z] (choice15 y z) := by decide +kernel

/-- All 4096 tuples with first column 6, including their singular cases. -/
public theorem witnessRep6 (x y z : Fin 16)
    (hinj : ∀ i : Fin 16, act ![6, x, y, z] i = 0 → i = 0) :
    ∃ w : List (Fin 4), (evalMat ![6, x, y, z] w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat ![6, x, y, z] w ≠ localTable j := by
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
