module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Evaluation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows06
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates.Second.Rows10

/-!
# The second native fifth-compound certificate

All 462 rows are checked by bitwise parallel Laplace expansion. The packed
input masks are certified against the literal native generator and the exact
lexicographic five-subset enumeration. Taking an output bit recovers the
Boolean determinant evaluator, whose soundness gives the actual 5-by-5 minor.
This proves the saved matrix equality without any representation, presentation,
irreducibility or spectrum premise.

Sources: James, J. Algebra 27 (1973), 57–111; GM02 Proposition 5.1;
`NativeActions/source/README.md` fixes the column convention.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates

private lemma packedRow_second (i : Fin 462) :
    Second.packedRow i = exteriorRowsB[i.val]! := by
  have h (b : Fin 11) (r : Fin 42) :
      Second.packedRow (Second.rowIndex b r) = exteriorRowsB[(Second.rowIndex b r).val]! := by
    fin_cases b
    · exact Second.rows00 r
    · exact Second.rows01 r
    · exact Second.rows02 r
    · exact Second.rows03 r
    · exact Second.rows04 r
    · exact Second.rows05 r
    · exact Second.rows06 r
    · exact Second.rows07 r
    · exact Second.rows08 r
    · exact Second.rows09 r
    · exact Second.rows10 r
  let b : Fin 11 := ⟨i.val / 42, by omega⟩
  let r : Fin 42 := ⟨i.val % 42, by omega⟩
  have hi : Second.rowIndex b r = i := by
    apply Fin.ext
    dsimp [Second.rowIndex, b, r]
    omega
  rw [← hi]
  exact h b r

/-- The literal fifth compound matrix of the native second generator, in column convention. -/
theorem compoundMatrix_second : compoundMatrix (codeMatrix true) = exteriorMatrix true := by
  apply compoundMatrix_eq_of_bits true
  intro i j
  change compoundBit true i j = (exteriorRowsB[i.val]!).testBit j.val
  rw [← Second.packedRow_testBit, packedRow_second]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.ExteriorCoordinates
