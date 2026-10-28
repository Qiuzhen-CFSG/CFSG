module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Commutant.Checks
/-!
# Bounded-cost scan certificates for the max4 commutant

A zero mask selects no rows. Skipping it, and skipping XOR with zero at each
unset bit, avoids repeated reduction of unused table tails. The soundness
lemma identifies this evaluator with the exact `scan` used in `Checks`.
The following adapters discharge the literal contracts consumed by
`Reduction.lowerTriangular_of_checks` without changing their tables.

Source: `../source/README.md` and `../../source/reconstruction.json`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof.Calibration

def skipScan : Nat → List Nat → Nat
  | _, [] => 0
  | x, y :: ys => if x = 0 then 0 else if x.testBit 0 then y ^^^ skipScan (x / 2) ys
    else skipScan (x / 2) ys

lemma scan_zero (xs : List Nat) : scan 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    change 0 ^^^ scan 0 ys = 0
    rw [Nat.zero_xor, ih]

lemma skipScan_eq (x : Nat) (xs : List Nat) : skipScan x xs = scan x xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    rw [skipScan]
    split
    · next h => simp [h, scan_zero]
    · simp only [scan, Nat.shiftRight_one]
      split <;> simp_all only [Nat.zero_xor]

/-- Bit extraction by division avoids iterating a right shift at every matrix entry. -/
theorem column_of_div (a : Fin 11)
    (h : ∀ i j : Fin 112,
      (columns.get a).get j / 2 ^ i.val % 2 = (differences.get a).get i / 2 ^ j.val % 2) :
    ColumnCheck a := by
  intro i j
  simp only [Nat.testBit_eq_decide_div_mod_eq, h i j]

theorem inverse_of_skip (i : Fin 112)
    (h : skipScan (inverseRows.get i) orbitRows.toList = 2 ^ i.val) : InverseCheck i := by
  simpa only [InverseCheck, skipScan_eq] using h

theorem small_of_skip (i : Fin 112)
    (h : skipScan (smallRows.get i) orbitRows.toList =
      skipScan (orbitRows.get i) difference0.toList) : SmallCheck i := by
  simpa only [SmallCheck, skipScan_eq] using h

theorem equation_of_skip (t : Fin 418)
    (h : let ij := equationPositions.get t
      equationRows.get t =
        skipScan (column0.get ij.2) (expressions.get ij.1).toList ^^^
          skipScan (smallRows.get ij.1) (expressionColumns.get ij.2).toList) :
    EquationCheck t := by
  simpa only [EquationCheck, skipScan_eq] using h

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo.CommutantProof.Calibration
