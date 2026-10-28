module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Arithmetic
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Columns.Data

/-!
# Assembly of shared reverse-norm word columns

Each distinct literal word is checked once. The nine original generators then
reuse those checks, with every occurrence retained. The independent row check
compares the resulting XORs with the original arrays. This gives precisely
`ColumnChecks`, without assuming correctness of either subgroup-action cache.

Source: Coefficients/source/README.md and Columns/source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
namespace Columns

/-- The candidate column of one literal word at one original output root. -/
def candidate (d : Fin 26) (j : Fin 1008) : Nat :=
  (blockGet (wordColumns d) (j.val / 16) >>> (1008 * (j.val % 16))) % 2 ^ 1008

/-- The original list of occurrences, now referring to the shared catalogue. -/
def combined (k : Fin 9) (j : Fin 1008) : Nat :=
  xorList ((indices k).map fun d => candidate d j)

/-- The complete finite arithmetic contract for one distinct literal word. -/
def WordChecks (d : Fin 26) : Prop :=
  ∀ j : Fin 1008, wordColumn leftAction rightAction (words d) j = candidate d j

/-- A consecutive portion of the catalogue; endpoints are ordinary naturals. -/
def WordChecksIn (first stop : Nat) : Prop :=
  ∀ d : Fin 26, first ≤ d.val → d.val < stop → WordChecks d

/-- The independent comparison with the unchanged original row arrays. -/
def RowChecks : Prop :=
  ∀ (k : Fin 9) (j : Fin 1008), combined k j = columnFromRows j.val (rows k).toList

theorem column_eq_combined (h : ∀ d, WordChecks d) (k : Fin 9) (j : Fin 1008) :
    column leftAction rightAction k j = combined k j := by
  unfold column combined
  rw [generatorWords_eq_catalogue]
  change ∀ d j, wordColumn leftAction rightAction (words d) j = candidate d j at h
  simp only [List.map_map, Function.comp_def, h]

/-- Four disjoint families cover all 26 words, with no word omitted. -/
theorem wordChecks_of_ranges
    (h₀ : WordChecksIn 0 7) (h₁ : WordChecksIn 7 14)
    (h₂ : WordChecksIn 14 20) (h₃ : WordChecksIn 20 26) : ∀ d, WordChecks d := by
  intro d
  by_cases h7 : d.val < 7
  · exact h₀ d (Nat.zero_le _) h7
  by_cases h14 : d.val < 14
  · exact h₁ d (by omega) h14
  by_cases h20 : d.val < 20
  · exact h₂ d (by omega) h20
  · exact h₃ d (by omega) d.isLt

end Columns

/-- Discharge the exact packed-column contract from the two finite checks. -/
theorem columnChecks_of_shared_words
    (hwords : ∀ d, Columns.WordChecks d) (hrows : Columns.RowChecks) : ColumnChecks := by
  intro k j
  exact (Columns.column_eq_combined hwords k j).trans (hrows k j)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
