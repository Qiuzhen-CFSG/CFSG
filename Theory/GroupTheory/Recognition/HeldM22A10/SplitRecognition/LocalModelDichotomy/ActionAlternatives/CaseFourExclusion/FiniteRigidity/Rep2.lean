module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Witnesses

/-!
# Case IV certificates with first column 2

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
    Check ![2, 0, y, z] (choice0 y z) := by decide +kernel

private def choice1 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inl 12, .inl 14, .inl 13, .inl 15, .inr 0, .inr 1, .inr 1, .inr 0, .inr 0, .inr 1, .inr 1, .inr 0],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inl 14, .inl 12, .inl 15, .inl 13, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inl 13, .inl 15, .inl 12, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inl 15, .inl 13, .inl 14, .inl 12, .inr 0, .inr 1, .inr 1, .inr 0, .inr 1, .inr 0, .inr 0, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 0, .inr 0, .inr 1, .inr 1, .inl 12, .inl 14, .inl 13, .inl 15, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 0, .inr 0, .inl 14, .inl 12, .inl 15, .inl 13, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 0, .inr 0, .inr 1, .inr 1, .inl 13, .inl 15, .inl 12, .inl 14, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 0, .inr 0, .inl 15, .inl 13, .inl 14, .inl 12, .inr 1, .inr 1, .inr 1, .inr 1],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 1, .inr 1, .inr 0, .inr 0, .inr 1, .inr 1, .inl 12, .inl 14, .inl 13, .inl 15],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 0, .inr 0, .inl 14, .inl 12, .inl 15, .inl 13],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 1, .inr 0, .inr 0, .inl 13, .inl 15, .inl 12, .inl 14],
    ![.inl 8, .inl 10, .inl 9, .inl 11, .inr 1, .inr 1, .inr 1, .inr 1, .inr 0, .inr 0, .inr 1, .inr 1, .inl 15, .inl 13, .inl 14, .inl 12]]

private theorem check1 : ∀ y z : Fin 16,
    Check ![2, 1, y, z] (choice1 y z) := by decide +kernel

private def choice2 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
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

private theorem check2 : ∀ y z : Fin 16,
    Check ![2, 2, y, z] (choice2 y z) := by decide +kernel

private def choice3 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inl 12, .inl 15, .inl 13, .inl 14, .inr 2, .inr 3, .inr 3, .inr 2, .inr 4, .inr 3, .inr 3, .inr 4],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inl 15, .inl 12, .inl 14, .inl 13, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inl 13, .inl 14, .inl 12, .inl 15, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inl 14, .inl 13, .inl 15, .inl 12, .inr 3, .inr 2, .inr 2, .inr 3, .inr 4, .inr 3, .inr 3, .inr 4],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 3, .inr 3, .inl 12, .inl 15, .inl 13, .inl 14, .inr 2, .inr 4, .inr 3, .inr 3],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 3, .inr 3, .inl 15, .inl 12, .inl 14, .inl 13, .inr 3, .inr 3, .inr 4, .inr 2],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 3, .inr 3, .inl 13, .inl 14, .inl 12, .inl 15, .inr 3, .inr 3, .inr 4, .inr 2],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 3, .inr 3, .inl 14, .inl 13, .inl 15, .inl 12, .inr 2, .inr 4, .inr 3, .inr 3],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 2, .inr 4, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inl 12, .inl 15, .inl 13, .inl 14],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 2, .inr 4, .inr 3, .inr 3, .inr 3, .inr 3, .inl 15, .inl 12, .inl 14, .inl 13],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 4, .inr 2, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inr 3, .inl 13, .inl 14, .inl 12, .inl 15],
    ![.inl 8, .inl 11, .inl 9, .inl 10, .inr 3, .inr 3, .inr 4, .inr 2, .inr 3, .inr 3, .inr 3, .inr 3, .inl 14, .inl 13, .inl 15, .inl 12]]

private theorem check3 : ∀ y z : Fin 16,
    Check ![2, 3, y, z] (choice3 y z) := by decide +kernel

private def choice4 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inl 10, .inl 14, .inl 11, .inl 15, .inr 5, .inr 4, .inr 4, .inr 5, .inr 4, .inr 5, .inr 5, .inr 4],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inl 10, .inl 15, .inl 11, .inl 14, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inl 10, .inl 12, .inl 11, .inl 13, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inl 10, .inl 13, .inl 11, .inl 12, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 8, .inr 9, .inl 9, .inr 8, .inl 10, .inr 10, .inl 11, .inr 11, .inl 12, .inr 12, .inl 13, .inr 13, .inl 14, .inr 14, .inl 15, .inr 15],
    ![.inl 8, .inr 8, .inl 9, .inr 9, .inl 10, .inr 11, .inl 11, .inr 10, .inr 13, .inl 12, .inr 12, .inl 13, .inr 15, .inl 14, .inr 14, .inl 15],
    ![.inl 8, .inr 10, .inl 9, .inr 11, .inl 10, .inr 9, .inl 11, .inr 8, .inl 13, .inr 16, .inl 12, .inr 15, .inl 15, .inr 12, .inl 14, .inr 17],
    ![.inl 8, .inr 11, .inl 9, .inr 10, .inl 10, .inr 8, .inl 11, .inr 9, .inr 15, .inl 13, .inr 16, .inl 12, .inr 17, .inl 15, .inr 12, .inl 14],
    ![.inl 8, .inr 12, .inl 9, .inr 13, .inl 10, .inr 15, .inl 11, .inr 18, .inl 14, .inr 19, .inl 15, .inr 10, .inl 12, .inr 9, .inl 13, .inr 8],
    ![.inl 8, .inr 13, .inl 9, .inr 12, .inl 10, .inr 18, .inl 11, .inr 15, .inr 10, .inl 14, .inr 19, .inl 15, .inr 8, .inl 12, .inr 9, .inl 13],
    ![.inl 8, .inr 16, .inl 9, .inr 15, .inl 10, .inr 17, .inl 11, .inr 12, .inl 15, .inr 8, .inl 14, .inr 9, .inl 13, .inr 10, .inl 12, .inr 19],
    ![.inl 8, .inr 15, .inl 9, .inr 16, .inl 10, .inr 12, .inl 11, .inr 17, .inr 9, .inl 15, .inr 8, .inl 14, .inr 19, .inl 13, .inr 10, .inl 12]]

private theorem check4 : ∀ y z : Fin 16,
    Check ![2, 4, y, z] (choice4 y z) := by decide +kernel

private def choice5 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inl 14, .inl 10, .inl 15, .inl 11, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inl 15, .inl 10, .inl 14, .inl 11, .inr 5, .inr 4, .inr 4, .inr 5, .inr 5, .inr 4, .inr 4, .inr 5],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inl 12, .inl 10, .inl 13, .inl 11, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inl 13, .inl 10, .inl 12, .inl 11, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 10, .inl 9, .inr 11, .inr 9, .inl 10, .inr 8, .inl 11, .inl 12, .inr 15, .inl 13, .inr 14, .inr 13, .inl 14, .inr 12, .inl 15],
    ![.inl 8, .inr 11, .inl 9, .inr 10, .inr 8, .inl 10, .inr 9, .inl 11, .inr 14, .inl 12, .inr 15, .inl 13, .inl 14, .inr 12, .inl 15, .inr 13],
    ![.inl 8, .inr 9, .inl 9, .inr 8, .inr 10, .inl 10, .inr 11, .inl 11, .inl 13, .inr 17, .inl 12, .inr 12, .inr 15, .inl 15, .inr 16, .inl 14],
    ![.inl 8, .inr 8, .inl 9, .inr 9, .inr 11, .inl 10, .inr 10, .inl 11, .inr 12, .inl 13, .inr 17, .inl 12, .inl 15, .inr 16, .inl 14, .inr 15],
    ![.inl 8, .inr 18, .inl 9, .inr 15, .inr 13, .inl 10, .inr 12, .inl 11, .inr 9, .inl 14, .inr 8, .inl 15, .inl 12, .inr 19, .inl 13, .inr 10],
    ![.inl 8, .inr 15, .inl 9, .inr 18, .inr 12, .inl 10, .inr 13, .inl 11, .inl 14, .inr 8, .inl 15, .inr 9, .inr 10, .inl 12, .inr 19, .inl 13],
    ![.inl 8, .inr 12, .inl 9, .inr 17, .inr 15, .inl 10, .inr 16, .inl 11, .inr 10, .inl 15, .inr 19, .inl 14, .inl 13, .inr 8, .inl 12, .inr 9],
    ![.inl 8, .inr 17, .inl 9, .inr 12, .inr 16, .inl 10, .inr 15, .inl 11, .inl 15, .inr 19, .inl 14, .inr 10, .inr 9, .inl 13, .inr 8, .inl 12]]

private theorem check5 : ∀ y z : Fin 16,
    Check ![2, 5, y, z] (choice5 y z) := by decide +kernel

private def choice6 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inl 11, .inl 15, .inl 10, .inl 14, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inl 11, .inl 14, .inl 10, .inl 15, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inl 11, .inl 12, .inl 10, .inl 13, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inl 11, .inl 13, .inl 10, .inl 12, .inr 5, .inr 4, .inr 4, .inr 5, .inr 5, .inr 4, .inr 4, .inr 5],
    ![.inl 8, .inr 17, .inl 9, .inr 20, .inl 11, .inr 12, .inl 10, .inr 13, .inl 12, .inr 19, .inl 13, .inr 10, .inl 15, .inr 8, .inl 14, .inr 9],
    ![.inl 8, .inr 20, .inl 9, .inr 17, .inl 11, .inr 13, .inl 10, .inr 12, .inr 10, .inl 12, .inr 19, .inl 13, .inr 9, .inl 15, .inr 8, .inl 14],
    ![.inl 8, .inr 12, .inl 9, .inr 13, .inl 11, .inr 20, .inl 10, .inr 17, .inl 13, .inr 8, .inl 12, .inr 9, .inl 14, .inr 19, .inl 15, .inr 10],
    ![.inl 8, .inr 13, .inl 9, .inr 12, .inl 11, .inr 17, .inl 10, .inr 20, .inr 9, .inl 13, .inr 8, .inl 12, .inr 10, .inl 14, .inr 19, .inl 15],
    ![.inl 8, .inr 10, .inl 9, .inr 11, .inl 11, .inr 8, .inl 10, .inr 9, .inl 15, .inr 12, .inl 14, .inr 13, .inl 12, .inr 17, .inl 13, .inr 20],
    ![.inl 8, .inr 11, .inl 9, .inr 10, .inl 11, .inr 9, .inl 10, .inr 8, .inr 13, .inl 15, .inr 12, .inl 14, .inr 20, .inl 12, .inr 17, .inl 13],
    ![.inl 8, .inr 9, .inl 9, .inr 8, .inl 11, .inr 11, .inl 10, .inr 10, .inl 14, .inr 17, .inl 15, .inr 20, .inl 13, .inr 13, .inl 12, .inr 12],
    ![.inl 8, .inr 8, .inl 9, .inr 9, .inl 11, .inr 10, .inl 10, .inr 11, .inr 20, .inl 14, .inr 17, .inl 15, .inr 12, .inl 13, .inr 13, .inl 12]]

private theorem check6 : ∀ y z : Fin 16,
    Check ![2, 6, y, z] (choice6 y z) := by decide +kernel

private def choice7 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inl 15, .inl 11, .inl 14, .inl 10, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8, .inr 8],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inl 14, .inl 11, .inl 15, .inl 10, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7, .inr 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inl 12, .inl 11, .inl 13, .inl 10, .inr 5, .inr 4, .inr 4, .inr 5, .inr 4, .inr 5, .inr 5, .inr 4],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inl 13, .inl 11, .inl 12, .inl 10, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6, .inr 6],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 13, .inl 9, .inr 12, .inr 20, .inl 11, .inr 17, .inl 10, .inl 12, .inr 8, .inl 13, .inr 9, .inr 19, .inl 15, .inr 10, .inl 14],
    ![.inl 8, .inr 12, .inl 9, .inr 13, .inr 17, .inl 11, .inr 20, .inl 10, .inr 9, .inl 12, .inr 8, .inl 13, .inl 15, .inr 10, .inl 14, .inr 19],
    ![.inl 8, .inr 17, .inl 9, .inr 20, .inr 13, .inl 11, .inr 12, .inl 10, .inl 13, .inr 19, .inl 12, .inr 10, .inr 8, .inl 14, .inr 9, .inl 15],
    ![.inl 8, .inr 20, .inl 9, .inr 17, .inr 12, .inl 11, .inr 13, .inl 10, .inr 10, .inl 13, .inr 19, .inl 12, .inl 14, .inr 9, .inl 15, .inr 8],
    ![.inl 8, .inr 8, .inl 9, .inr 9, .inr 10, .inl 11, .inr 11, .inl 10, .inr 20, .inl 15, .inr 17, .inl 14, .inl 12, .inr 13, .inl 13, .inr 12],
    ![.inl 8, .inr 9, .inl 9, .inr 8, .inr 11, .inl 11, .inr 10, .inl 10, .inl 15, .inr 17, .inl 14, .inr 20, .inr 12, .inl 12, .inr 13, .inl 13],
    ![.inl 8, .inr 11, .inl 9, .inr 10, .inr 9, .inl 11, .inr 8, .inl 10, .inr 12, .inl 14, .inr 13, .inl 15, .inl 13, .inr 20, .inl 12, .inr 17],
    ![.inl 8, .inr 10, .inl 9, .inr 11, .inr 8, .inl 11, .inr 9, .inl 10, .inl 14, .inr 13, .inl 15, .inr 12, .inr 17, .inl 13, .inr 20, .inl 12]]

private theorem check7 : ∀ y z : Fin 16,
    Check ![2, 7, y, z] (choice7 y z) := by decide +kernel

private def choice8 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 8, .inr 10, .inr 9, .inr 21, .inl 10, .inl 14, .inl 11, .inl 15, .inr 19, .inr 16, .inr 22, .inr 23],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 10, .inr 8, .inr 24, .inr 9, .inl 10, .inl 15, .inl 11, .inl 14, .inr 25, .inr 19, .inr 23, .inr 22],
    ![.inl 8, .inr 26, .inl 9, .inr 5, .inl 12, .inr 27, .inl 13, .inr 28, .inl 10, .inr 6, .inl 11, .inr 29, .inl 14, .inr 10, .inl 15, .inr 30],
    ![.inl 8, .inr 4, .inl 9, .inr 5, .inr 27, .inl 12, .inr 28, .inl 13, .inl 10, .inr 6, .inl 11, .inr 29, .inr 9, .inl 14, .inr 8, .inl 15],
    ![.inl 8, .inr 4, .inl 9, .inr 5, .inl 13, .inr 28, .inl 12, .inr 27, .inl 10, .inr 6, .inl 11, .inr 29, .inl 15, .inr 30, .inl 14, .inr 8],
    ![.inl 8, .inr 26, .inl 9, .inr 5, .inr 28, .inl 13, .inr 27, .inl 12, .inl 10, .inr 6, .inl 11, .inr 29, .inr 30, .inl 15, .inr 31, .inl 14],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 9, .inr 21, .inr 8, .inr 10, .inl 10, .inl 12, .inl 11, .inl 13, .inr 22, .inr 23, .inr 19, .inr 32],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 21, .inr 9, .inr 10, .inr 8, .inl 10, .inl 13, .inl 11, .inl 12, .inr 24, .inr 33, .inr 16, .inr 19],
    ![.inl 8, .inr 4, .inl 9, .inr 5, .inl 14, .inr 34, .inl 15, .inr 30, .inl 10, .inr 6, .inl 11, .inr 29, .inl 12, .inr 27, .inl 13, .inr 28],
    ![.inl 8, .inr 26, .inl 9, .inr 5, .inr 34, .inl 14, .inr 30, .inl 15, .inl 10, .inr 6, .inl 11, .inr 29, .inr 27, .inl 12, .inr 28, .inl 13],
    ![.inl 8, .inr 26, .inl 9, .inr 5, .inl 15, .inr 30, .inl 14, .inr 34, .inl 10, .inr 6, .inl 11, .inr 29, .inl 13, .inr 28, .inl 12, .inr 27],
    ![.inl 8, .inr 4, .inl 9, .inr 5, .inr 30, .inl 15, .inr 19, .inl 14, .inl 10, .inr 6, .inl 11, .inr 29, .inr 28, .inl 13, .inr 27, .inl 12]]

private theorem check8 : ∀ y z : Fin 16,
    Check ![2, 8, y, z] (choice8 y z) := by decide +kernel

private def choice9 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 9, .inr 21, .inr 8, .inr 10, .inl 14, .inl 10, .inl 15, .inl 11, .inr 23, .inr 22, .inr 16, .inr 19],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 24, .inr 9, .inr 10, .inr 8, .inl 15, .inl 10, .inl 14, .inl 11, .inr 22, .inr 23, .inr 19, .inr 25],
    ![.inl 8, .inr 5, .inl 9, .inr 26, .inl 12, .inr 28, .inl 13, .inr 27, .inr 29, .inl 10, .inr 6, .inl 11, .inr 30, .inl 14, .inr 10, .inl 15],
    ![.inl 8, .inr 5, .inl 9, .inr 4, .inr 28, .inl 12, .inr 27, .inl 13, .inr 29, .inl 10, .inr 6, .inl 11, .inl 14, .inr 8, .inl 15, .inr 9],
    ![.inl 8, .inr 5, .inl 9, .inr 4, .inl 13, .inr 27, .inl 12, .inr 28, .inr 29, .inl 10, .inr 6, .inl 11, .inr 8, .inl 15, .inr 30, .inl 14],
    ![.inl 8, .inr 5, .inl 9, .inr 26, .inr 27, .inl 13, .inr 28, .inl 12, .inr 29, .inl 10, .inr 6, .inl 11, .inl 15, .inr 31, .inl 14, .inr 30],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 8, .inr 10, .inr 9, .inr 21, .inl 12, .inl 10, .inl 13, .inl 11, .inr 32, .inr 19, .inr 23, .inr 22],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 10, .inr 8, .inr 21, .inr 9, .inl 13, .inl 10, .inl 12, .inl 11, .inr 19, .inr 16, .inr 33, .inr 24],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inr 5, .inl 9, .inr 26, .inr 30, .inl 14, .inr 34, .inl 15, .inr 29, .inl 10, .inr 6, .inl 11, .inl 12, .inr 28, .inl 13, .inr 27],
    ![.inl 8, .inr 5, .inl 9, .inr 4, .inl 14, .inr 30, .inl 15, .inr 34, .inr 29, .inl 10, .inr 6, .inl 11, .inr 28, .inl 12, .inr 27, .inl 13],
    ![.inl 8, .inr 5, .inl 9, .inr 4, .inr 19, .inl 15, .inr 30, .inl 14, .inr 29, .inl 10, .inr 6, .inl 11, .inl 13, .inr 27, .inl 12, .inr 28],
    ![.inl 8, .inr 5, .inl 9, .inr 26, .inl 15, .inr 34, .inl 14, .inr 30, .inr 29, .inl 10, .inr 6, .inl 11, .inr 27, .inl 13, .inr 28, .inl 12]]

private theorem check9 : ∀ y z : Fin 16,
    Check ![2, 9, y, z] (choice9 y z) := by decide +kernel

private def choice10 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 19, .inr 25, .inr 22, .inr 23, .inl 11, .inl 15, .inl 10, .inl 14, .inr 9, .inr 24, .inr 8, .inr 10],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 16, .inr 19, .inr 23, .inr 22, .inl 11, .inl 14, .inl 10, .inl 15, .inr 21, .inr 9, .inr 10, .inr 8],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inl 12, .inr 30, .inl 13, .inr 31, .inl 11, .inr 5, .inl 10, .inr 26, .inl 15, .inr 27, .inl 14, .inr 28],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inr 30, .inl 12, .inr 8, .inl 13, .inl 11, .inr 5, .inl 10, .inr 4, .inr 27, .inl 15, .inr 28, .inl 14],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inl 13, .inr 9, .inl 12, .inr 8, .inl 11, .inr 5, .inl 10, .inr 4, .inl 14, .inr 28, .inl 15, .inr 27],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inr 10, .inl 13, .inr 30, .inl 12, .inl 11, .inr 5, .inl 10, .inr 26, .inr 28, .inl 14, .inr 27, .inl 15],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 23, .inr 22, .inr 32, .inr 19, .inl 11, .inl 12, .inl 10, .inl 13, .inr 10, .inr 8, .inr 21, .inr 9],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 33, .inr 24, .inr 19, .inr 16, .inl 11, .inl 13, .inl 10, .inl 12, .inr 8, .inr 10, .inr 9, .inr 21],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inl 15, .inr 27, .inl 14, .inr 28, .inl 11, .inr 5, .inl 10, .inr 26, .inl 12, .inr 30, .inl 13, .inr 34],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inr 27, .inl 15, .inr 28, .inl 14, .inl 11, .inr 5, .inl 10, .inr 4, .inr 30, .inl 12, .inr 34, .inl 13],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inl 14, .inr 28, .inl 15, .inr 27, .inl 11, .inr 5, .inl 10, .inr 4, .inl 13, .inr 19, .inl 12, .inr 30],
    ![.inl 8, .inr 6, .inl 9, .inr 29, .inr 28, .inl 14, .inr 27, .inl 15, .inl 11, .inr 5, .inl 10, .inr 26, .inr 34, .inl 13, .inr 30, .inl 12]]

private theorem check10 : ∀ y z : Fin 16,
    Check ![2, 10, y, z] (choice10 y z) := by decide +kernel

private def choice11 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 22, .inr 23, .inr 19, .inr 25, .inl 15, .inl 11, .inl 14, .inl 10, .inr 10, .inr 8, .inr 24, .inr 9],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 23, .inr 22, .inr 16, .inr 19, .inl 14, .inl 11, .inl 15, .inl 10, .inr 8, .inr 10, .inr 9, .inr 21],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inl 12, .inr 31, .inl 13, .inr 30, .inr 26, .inl 11, .inr 5, .inl 10, .inr 28, .inl 15, .inr 27, .inl 14],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inr 8, .inl 12, .inr 30, .inl 13, .inr 4, .inl 11, .inr 5, .inl 10, .inl 15, .inr 28, .inl 14, .inr 27],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inl 13, .inr 8, .inl 12, .inr 9, .inr 4, .inl 11, .inr 5, .inl 10, .inr 27, .inl 14, .inr 28, .inl 15],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inr 30, .inl 13, .inr 10, .inl 12, .inr 26, .inl 11, .inr 5, .inl 10, .inl 14, .inr 27, .inl 15, .inr 28],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 32, .inr 19, .inr 23, .inr 22, .inl 12, .inl 11, .inl 13, .inl 10, .inr 9, .inr 21, .inr 8, .inr 10],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 19, .inr 16, .inr 33, .inr 24, .inl 13, .inl 11, .inl 12, .inl 10, .inr 21, .inr 9, .inr 10, .inr 8],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inr 28, .inl 15, .inr 27, .inl 14, .inr 4, .inl 11, .inr 5, .inl 10, .inl 12, .inr 34, .inl 13, .inr 30],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inl 15, .inr 28, .inl 14, .inr 27, .inr 26, .inl 11, .inr 5, .inl 10, .inr 34, .inl 12, .inr 30, .inl 13],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inr 27, .inl 14, .inr 28, .inl 15, .inr 26, .inl 11, .inr 5, .inl 10, .inl 13, .inr 30, .inl 12, .inr 34],
    ![.inl 8, .inr 29, .inl 9, .inr 6, .inl 14, .inr 27, .inl 15, .inr 28, .inr 4, .inl 11, .inr 5, .inl 10, .inr 30, .inl 13, .inr 19, .inl 12]]

private theorem check11 : ∀ y z : Fin 16,
    Check ![2, 11, y, z] (choice11 y z) := by decide +kernel

private def choice12 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 10, .inr 8, .inr 21, .inr 9, .inr 16, .inr 17, .inr 23, .inr 19, .inl 10, .inl 14, .inl 11, .inl 15],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 9, .inr 24, .inr 8, .inr 10, .inr 19, .inr 23, .inr 17, .inr 16, .inl 10, .inl 15, .inl 11, .inl 14],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inl 12, .inr 26, .inl 13, .inr 5, .inl 14, .inr 7, .inl 15, .inr 6, .inl 10, .inr 30, .inl 11, .inr 31],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inr 4, .inl 12, .inr 5, .inl 13, .inr 7, .inl 14, .inr 6, .inl 15, .inl 10, .inr 30, .inl 11, .inr 8],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inl 13, .inr 5, .inl 12, .inr 4, .inl 15, .inr 6, .inl 14, .inr 7, .inl 10, .inr 8, .inl 11, .inr 10],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inr 5, .inl 13, .inr 26, .inl 12, .inr 6, .inl 15, .inr 7, .inl 14, .inl 10, .inr 30, .inl 11, .inr 34],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inl 14, .inr 7, .inl 15, .inr 6, .inl 12, .inr 4, .inl 13, .inr 5, .inl 10, .inr 30, .inl 11, .inr 17],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inr 7, .inl 14, .inr 6, .inl 15, .inr 26, .inl 12, .inr 5, .inl 13, .inl 10, .inr 30, .inl 11, .inr 35],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inl 15, .inr 6, .inl 14, .inr 7, .inl 13, .inr 5, .inl 12, .inr 26, .inl 10, .inr 30, .inl 11, .inr 35],
    ![.inl 8, .inr 27, .inl 9, .inr 28, .inr 6, .inl 15, .inr 7, .inl 14, .inr 5, .inl 13, .inr 4, .inl 12, .inl 10, .inr 30, .inl 11, .inr 34],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 23, .inr 19, .inr 32, .inr 17, .inr 21, .inr 9, .inr 10, .inr 8, .inl 10, .inl 12, .inl 11, .inl 13],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 17, .inr 16, .inr 19, .inr 24, .inr 8, .inr 10, .inr 9, .inr 21, .inl 10, .inl 13, .inl 11, .inl 12]]

private theorem check12 : ∀ y z : Fin 16,
    Check ![2, 12, y, z] (choice12 y z) := by decide +kernel

private def choice13 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 21, .inr 9, .inr 10, .inr 8, .inr 19, .inr 23, .inr 17, .inr 16, .inl 14, .inl 10, .inl 15, .inl 11],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 8, .inr 10, .inr 9, .inr 24, .inr 16, .inr 17, .inr 23, .inr 19, .inl 15, .inl 10, .inl 14, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inl 12, .inr 5, .inl 13, .inr 26, .inr 6, .inl 14, .inr 7, .inl 15, .inr 31, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inr 5, .inl 12, .inr 4, .inl 13, .inl 14, .inr 6, .inl 15, .inr 7, .inr 8, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inl 13, .inr 4, .inl 12, .inr 5, .inr 7, .inl 15, .inr 6, .inl 14, .inr 10, .inl 10, .inr 8, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inr 26, .inl 13, .inr 5, .inl 12, .inl 15, .inr 7, .inl 14, .inr 6, .inr 34, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inr 6, .inl 14, .inr 7, .inl 15, .inl 12, .inr 5, .inl 13, .inr 26, .inr 35, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inl 14, .inr 6, .inl 15, .inr 7, .inr 5, .inl 12, .inr 4, .inl 13, .inr 17, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inr 7, .inl 15, .inr 6, .inl 14, .inl 13, .inr 4, .inl 12, .inr 5, .inr 34, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inr 28, .inl 9, .inr 27, .inl 15, .inr 7, .inl 14, .inr 6, .inr 26, .inl 13, .inr 5, .inl 12, .inr 35, .inl 10, .inr 30, .inl 11],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 32, .inr 17, .inr 23, .inr 19, .inr 8, .inr 10, .inr 9, .inr 21, .inl 12, .inl 10, .inl 13, .inl 11],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 19, .inr 24, .inr 17, .inr 16, .inr 21, .inr 9, .inr 10, .inr 8, .inl 13, .inl 10, .inl 12, .inl 11],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7]]

private theorem check13 : ∀ y z : Fin 16,
    Check ![2, 13, y, z] (choice13 y z) := by decide +kernel

private def choice14 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 16, .inr 17, .inr 23, .inr 19, .inr 24, .inr 9, .inr 10, .inr 8, .inl 11, .inl 15, .inl 10, .inl 14],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 19, .inr 23, .inr 17, .inr 16, .inr 8, .inr 10, .inr 9, .inr 21, .inl 11, .inl 14, .inl 10, .inl 15],
    ![.inl 8, .inr 34, .inl 9, .inr 30, .inl 12, .inr 7, .inl 13, .inr 6, .inl 15, .inr 5, .inl 14, .inr 26, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 10, .inl 9, .inr 8, .inr 7, .inl 12, .inr 6, .inl 13, .inr 5, .inl 15, .inr 4, .inl 14, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 8, .inl 9, .inr 30, .inl 13, .inr 6, .inl 12, .inr 7, .inl 14, .inr 4, .inl 15, .inr 5, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 31, .inl 9, .inr 30, .inr 6, .inl 13, .inr 7, .inl 12, .inr 26, .inl 14, .inr 5, .inl 15, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 35, .inl 9, .inr 30, .inl 15, .inr 5, .inl 14, .inr 26, .inl 12, .inr 7, .inl 13, .inr 6, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 17, .inl 9, .inr 30, .inr 5, .inl 15, .inr 4, .inl 14, .inr 7, .inl 12, .inr 6, .inl 13, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 34, .inl 9, .inr 30, .inl 14, .inr 4, .inl 15, .inr 5, .inl 13, .inr 6, .inl 12, .inr 7, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 8, .inr 35, .inl 9, .inr 30, .inr 26, .inl 14, .inr 5, .inl 15, .inr 6, .inl 13, .inr 7, .inl 12, .inl 11, .inr 27, .inl 10, .inr 28],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 8, .inr 10, .inr 9, .inr 21, .inr 19, .inr 23, .inr 17, .inr 32, .inl 11, .inl 12, .inl 10, .inl 13],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 21, .inr 9, .inr 10, .inr 8, .inr 16, .inr 17, .inr 24, .inr 19, .inl 11, .inl 13, .inl 10, .inl 12]]

private theorem check14 : ∀ y z : Fin 16,
    Check ![2, 14, y, z] (choice14 y z) := by decide +kernel

private def choice15 : Fin 16 → Fin 16 → Fin 16 ⊕ Fin 78 :=
  ![
    ![.inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4, .inl 4],
    ![.inl 8, .inl 12, .inl 9, .inl 13, .inr 23, .inr 19, .inr 16, .inr 17, .inr 8, .inr 10, .inr 9, .inr 24, .inl 15, .inl 11, .inl 14, .inl 10],
    ![.inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5, .inl 5],
    ![.inl 8, .inl 13, .inl 9, .inl 12, .inr 17, .inr 16, .inr 19, .inr 23, .inr 21, .inr 9, .inr 10, .inr 8, .inl 14, .inl 11, .inl 15, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 34, .inl 12, .inr 6, .inl 13, .inr 7, .inr 26, .inl 15, .inr 5, .inl 14, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 8, .inl 9, .inr 10, .inr 6, .inl 12, .inr 7, .inl 13, .inl 15, .inr 4, .inl 14, .inr 5, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 8, .inl 13, .inr 7, .inl 12, .inr 6, .inr 5, .inl 14, .inr 4, .inl 15, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 31, .inr 7, .inl 13, .inr 6, .inl 12, .inl 14, .inr 5, .inl 15, .inr 26, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 17, .inr 4, .inl 15, .inr 5, .inl 14, .inl 12, .inr 6, .inl 13, .inr 7, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 35, .inl 15, .inr 26, .inl 14, .inr 5, .inr 6, .inl 12, .inr 7, .inl 13, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 35, .inr 5, .inl 14, .inr 26, .inl 15, .inl 13, .inr 7, .inl 12, .inr 6, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inr 30, .inl 9, .inr 34, .inl 14, .inr 5, .inl 15, .inr 4, .inr 7, .inl 13, .inr 6, .inl 12, .inr 28, .inl 11, .inr 27, .inl 10],
    ![.inl 8, .inl 15, .inl 9, .inl 14, .inr 9, .inr 21, .inr 8, .inr 10, .inr 32, .inr 17, .inr 23, .inr 19, .inl 12, .inl 11, .inl 13, .inl 10],
    ![.inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7, .inl 7],
    ![.inl 8, .inl 14, .inl 9, .inl 15, .inr 10, .inr 8, .inr 21, .inr 9, .inr 19, .inr 24, .inr 17, .inr 16, .inl 13, .inl 11, .inl 12, .inl 10],
    ![.inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6, .inl 6]]

private theorem check15 : ∀ y z : Fin 16,
    Check ![2, 15, y, z] (choice15 y z) := by decide +kernel

/-- All 4096 tuples with first column 2, including their singular cases. -/
public theorem witnessRep2 (x y z : Fin 16)
    (hinj : ∀ i : Fin 16, act ![2, x, y, z] i = 0 → i = 0) :
    ∃ w : List (Fin 4), (evalMat ![2, x, y, z] w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat ![2, x, y, z] w ≠ localTable j := by
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
