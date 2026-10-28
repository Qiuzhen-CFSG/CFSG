module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word14
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word15
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word16
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word17
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word18
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsFourteenToTwenty.Word19

/-!
# Packed reverse-norm word columns, catalogue indices 14 through 19

The six literal words in this range are checked on all 126 blocks of eight
output roots. Each block is a kernel reduction of the cached left and right
actions, all 25 power pairs, and the reversed inverse literal word. The block
coverage theorem then exports the exact `WordChecksIn 14 20` contract.

Source: `Coefficients/Columns/source/README.md` and the fixed candidate data in
`Coefficients/Columns/Data.lean`.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

theorem wordChecks_fourteenToTwenty : WordChecksIn 14 20 := by
  intro d hd hstop
  have hd_cases : d.val = 14 ∨ d.val = 15 ∨ d.val = 16 ∨ d.val = 17 ∨
      d.val = 18 ∨ d.val = 19 := by omega
  rcases hd_cases with h | h | h | h | h | h
  · have heq : d = ⟨14, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_14
  · have heq : d = ⟨15, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_15
  · have heq : d = ⟨16, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_16
  · have heq : d = ⟨17, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_17
  · have heq : d = ⟨18, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_18
  · have heq : d = ⟨19, by decide⟩ := Fin.ext (by omega)
    subst d
    exact wordChecks_19

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns
