module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm.Frame

/-!
# Sequential mask traversal for the degree-252 norm

Consume the binary mask by division by two. The equality with the published
packed traversal is proved for every list and mask, so the numerical checks
below use exactly the original matrix decoder. This avoids repeatedly shifting
from the start of a mask at every row entry.

Source: the polynomial expression in `../../../source/density-252.json`,
documented in `../../source/README.md`. The correctness argument adapts the
saved `Scratch/M24Density/StructuralChecker.lean`; it retains ordinary XOR.
-/

@[expose] public section
open Representation.MathieuSmall.M22Recognition.DegreeThirty.NineSubmodule.InducedHeads.HermitianFiltration
open FactorAlgebras.Certificate MatrixChecks
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm

def combineRows : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: l, mask =>
      (if mask % 2 = 1 then a else 0) ^^^ combineRows l (mask / 2)

theorem combineRows_from (l : List ℕ) (mask start : ℕ) :
    combineRows l (mask >>> start) = combineListFrom l mask start := by
  induction l generalizing start with
  | nil => rfl
  | cons a l ih =>
    rw [combineRows, combineListFrom, ← Nat.shiftRight_succ, ih]
    have hb : (mask >>> start).testBit 0 = mask.testBit start := by simp
    simp only [Nat.testBit_zero] at hb
    congr 1
    split_ifs <;> simp_all

theorem combineRows_eq (l : List ℕ) (mask : ℕ) :
    combineRows l mask = combineList l mask :=
  combineRows_from l mask 0

theorem map_combineRows {a b c : List ℕ} (h : a.map (combineRows b) = c) :
    a.map (combineList b) = c := by
  rw [show combineRows b = combineList b from funext (combineRows_eq b)] at h
  exact h

/-- A traversal certificate supplies the actual first product in the frame reduction. -/
theorem generatorProduct_eq_of_traversal
    (h : c1.map (combineRows c2) = c3) :
    generatorProduct = matrix252 0 * matrix252 1 := by
  exact (matrix_product (n := 252) c1 c2 c3 (by decide +kernel)
    (product_rows c1 c2 c3 (by decide +kernel) (map_combineRows h))).symm

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.MatrixDensity.Degree252.Norm
