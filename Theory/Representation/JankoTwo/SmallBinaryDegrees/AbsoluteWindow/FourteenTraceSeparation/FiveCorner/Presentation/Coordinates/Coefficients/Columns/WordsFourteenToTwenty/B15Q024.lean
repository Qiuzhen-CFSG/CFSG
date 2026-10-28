module
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-! Kernel-checked packed word-column block for catalogue word 15, roots 192..199. -/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
theorem wordBlock_15_024 : WordBlock ⟨15, by decide⟩ ⟨24, by decide⟩ := by
  unfold WordBlock
  intro r
  fin_cases r <;> rfl

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns
