module

public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality.Permutations
import Mathlib.Tactic.FinCases

/-!
# Comparing the compact tables with the original Held words

Homomorphism laws move the original He-valued words into the faithful
permutation representation. The compact intermediate ATLAS words avoid
repeated evaluation of long subexpressions. Every comparison is checked
on all 2058 points by Lean's kernel.

Source and reproduction: see Permutations.lean and Cardinality/source/generate.py.
-/

public section
namespace Held.OddCubeCandidates.CardinalityCertificates

set_option maxRecDepth 4096

private theorem representation_a : representation a = atlasA := rfl
private theorem representation_b : representation b = atlasB := rfl

theorem threeX_eq : threeX = representation threeFirst := by
  simp only [threeFirst, map_mul, map_pow, map_zpow, map_inv, representation_a,
    LocalPairs.PairCoverage.representation_localWord, Bool.false_eq_true, ite_false]
  rw [← fastLocalThree_eq, ← fastA_eq]
  apply Equiv.ext
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem threeY_eq : threeY = representation threeSecond := by
  simp only [threeSecond, map_mul, map_pow, map_inv, representation_a,
    LocalPairs.PairCoverage.representation_localWord, Bool.false_eq_true, ite_false]
  rw [← fastLocalThree_eq, ← fastA_eq]
  apply Equiv.ext
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem sevenX_eq : sevenX = representation sevenFirst := by
  simp only [sevenFirst, map_mul, map_pow, map_inv, representation_a, representation_b]
  rw [← fastLocalSeven_eq, ← fastB_eq]
  apply Equiv.ext
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

theorem sevenY_eq : sevenY = representation sevenSecond := by
  simp only [sevenSecond, map_mul, map_pow, map_zpow, representation_a, representation_b]
  rw [← fastLocalSeven_eq, ← fastB_eq]
  apply Equiv.ext
  apply allPoints
  intro q
  fin_cases q <;> apply allFin <;> decide +kernel

end Held.OddCubeCandidates.CardinalityCertificates
