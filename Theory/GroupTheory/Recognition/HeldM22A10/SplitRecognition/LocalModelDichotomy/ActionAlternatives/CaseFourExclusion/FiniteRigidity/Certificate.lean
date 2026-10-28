module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Rep2
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Rep4
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Rep6
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.CaseFourExclusion.FiniteRigidity.Rep8

/-!
# Exhaustion of the four Case IV orbit representatives

The four certificate families cover every tuple of last three columns. Their
singular branches contradict injectivity, and every remaining branch supplies
a word fixing the first vector outside the exact local group. The interpretation
of these columns and words on the actual binary group is proved in `Linear`.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed pp.2–3,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity

/-- A nonsingular matrix with any of the four reduced first columns generates
    a forbidden element of the first-vector stabilizer. -/
public theorem matrix_certificate (m : Mat) (k : Fin 4) (hm : m 0 = orbitRep k)
    (hinj : ∀ i : Fin 16, act m i = 0 → i = 0) :
    ∃ w : List (Fin 4), (evalMat m w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat m w ≠ localTable j := by
  have he : m = ![orbitRep k, m 1, m 2, m 3] := by
    funext i
    fin_cases i
    · exact hm
    · rfl
    · rfl
    · rfl
  have hi : ∀ i : Fin 16, act ![orbitRep k, m 1, m 2, m 3] i = 0 → i = 0 :=
    he ▸ hinj
  have h : ∃ w : List (Fin 4),
      (evalMat ![orbitRep k, m 1, m 2, m 3] w) 0 = 1 ∧
      ∀ j : Fin 8, evalMat ![orbitRep k, m 1, m 2, m 3] w ≠ localTable j := by
    fin_cases k
    · exact witnessRep2 _ _ _ hi
    · exact witnessRep4 _ _ _ hi
    · exact witnessRep6 _ _ _ hi
    · exact witnessRep8 _ _ _ hi
  simpa only [← he] using h

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy.CaseFour.FiniteRigidity
