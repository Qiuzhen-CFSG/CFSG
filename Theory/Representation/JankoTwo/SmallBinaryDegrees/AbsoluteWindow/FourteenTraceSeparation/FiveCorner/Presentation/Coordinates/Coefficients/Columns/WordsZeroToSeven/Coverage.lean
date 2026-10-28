module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Blocks

/-!
# Assembly of four bounded word checks

The intervals [0,32), [32,64), [64,96), and [96,126) partition the original
block indices. Explicit equalities of finite indices transport each block
proof without unfolding the numerical word calculation.

Source: Columns/Blocks.lean and its exact 126-by-8 output-root coverage.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven

theorem wordChecks_of_quarters (d : Fin 26)
    (h0 : ∀ q : Fin 32, WordBlock d ⟨0 + q.val, by omega⟩)
    (h32 : ∀ q : Fin 32, WordBlock d ⟨32 + q.val, by omega⟩)
    (h64 : ∀ q : Fin 32, WordBlock d ⟨64 + q.val, by omega⟩)
    (h96 : ∀ q : Fin 30, WordBlock d ⟨96 + q.val, by omega⟩)
    : WordChecks d := by
  apply wordChecks_of_blocks d
  intro q
  by_cases b0 : q.val < 32
  · have e : (⟨0 + q.val, by omega⟩ : Fin 126) = q := Fin.ext (Nat.zero_add _)
    exact e ▸ h0 ⟨q.val, b0⟩
  by_cases b1 : q.val < 64
  · have e : (⟨32 + (q.val - 32), by omega⟩ : Fin 126) = q := by
      apply Fin.ext
      change 32 + (q.val - 32) = q.val
      omega
    exact e ▸ h32 ⟨q.val - 32, by omega⟩
  by_cases b2 : q.val < 96
  · have e : (⟨64 + (q.val - 64), by omega⟩ : Fin 126) = q := by
      apply Fin.ext
      change 64 + (q.val - 64) = q.val
      omega
    exact e ▸ h64 ⟨q.val - 64, by omega⟩
  · have e : (⟨96 + (q.val - 96), by omega⟩ : Fin 126) = q := by
      apply Fin.ext
      change 96 + (q.val - 96) = q.val
      omega
    exact e ▸ h96 ⟨q.val - 96, by omega⟩

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.Columns.WordsZeroToSeven
