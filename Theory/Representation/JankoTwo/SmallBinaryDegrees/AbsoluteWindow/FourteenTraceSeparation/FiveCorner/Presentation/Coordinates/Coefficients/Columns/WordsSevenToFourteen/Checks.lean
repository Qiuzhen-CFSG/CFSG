module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.WordsSevenToFourteen.Evaluation
import Mathlib.Tactic.FinCases

/-!
# A bounded certificate for literal word 7

This checks blocks 62--65, hence original output roots 496--527, for the
unchanged word at catalogue index 7. Each eight-root block is independently
checked by the kernel and transferred through `columnNat_eq`.

This is a partial numerical certificate, not `WordChecksIn 7 14`. The full
range still requires the other blocks and words. Source and conventions:
`Columns/source/README.md` and `Coefficients/Arithmetic.lean`.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsSevenToFourteen

/-- All 25 original power pairs for word 7 and output roots 496--527. -/
theorem word7_blocks62To66 :
    ∀ q : Fin 4, WordBlock 7 ⟨62 + q.val, by omega⟩ := by
  intro q
  apply wordBlock_of_evaluatedBlock
  fin_cases q <;> unfold evaluatedBlock <;> decide +kernel

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsSevenToFourteen
