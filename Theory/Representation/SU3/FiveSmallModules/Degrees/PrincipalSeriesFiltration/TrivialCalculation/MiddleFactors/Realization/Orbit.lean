module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Action

/-!
# A checked spanning tree for the published coset permutations

A breadth-first tree of the fixed 126-point permutation table gives induction
from point zero using the two displayed images. Every edge and every strict
depth decrease is checked by the kernel. This certifies transitivity for any
realization of that table, without relying on a GAP generation label.

Source: `MiddleFactors/source/witnesses.json`, generated from the unchanged
`standard_flag_data.txt`; Guralnick–Malle Proposition 4.3, Aschbacher–Smith K.2.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization

private def depthRows : Array ℕ := #[0, 1, 4, 5, 2, 7, 8, 3, 7, 9, 6, 6, 6, 3, 7, 10, 7, 8, 10, 9, 6, 7, 8, 6, 4, 7, 8, 8, 7, 8, 6, 9, 4, 8, 10, 8, 10, 7, 7, 10, 8, 7, 7, 8, 7, 6, 9, 5, 7, 9, 4, 7, 5, 8, 6, 9, 8, 9, 9, 10, 10, 8, 6, 8, 10, 8, 7, 5, 9, 9, 8, 9, 9, 7, 5, 7, 7, 8, 6, 7, 9, 9, 7, 9, 7, 5, 5, 6, 9, 9, 9, 9, 10, 8, 7, 11, 9, 8, 7, 8, 8, 8, 6, 9, 9, 6, 8, 6, 8, 10, 9, 10, 8, 8, 10, 7, 8, 8, 9, 8, 8, 8, 10, 9, 9, 7]
private def parentRows : Array ℕ := #[0, 0, 7, 2, 1, 12, 21, 4, 30, 35, 3, 3, 47, 4, 54, 58, 62, 5, 68, 70, 74, 78, 73, 67, 7, 87, 75, 8, 62, 8, 67, 97, 13, 41, 9, 82, 71, 10, 10, 103, 38, 107, 11, 79, 11, 86, 70, 50, 54, 97, 13, 105, 32, 14, 86, 116, 48, 40, 61, 57, 57, 16, 47, 51, 88, 44, 102, 50, 56, 113, 38, 35, 93, 20, 32, 20, 30, 21, 85, 45, 27, 22, 23, 33, 23, 24, 24, 52, 26, 27, 63, 119, 69, 76, 87, 36, 121, 66, 107, 98, 42, 125, 74, 113, 40, 52, 41, 85, 42, 81, 43, 96, 79, 82, 110, 78, 84, 98, 99, 94, 94, 84, 71, 117, 112, 102]
private def edgeRows : Array ℕ := #[0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0]

private def depth (i : Fin 126) : ℕ := depthRows[i.val]!

private theorem parent_lt : ∀ i : Fin 126, parentRows[i.val]! < 126 := by decide +kernel
private theorem edge_lt : ∀ i : Fin 126, edgeRows[i.val]! < 2 := by decide +kernel

private def predecessor (i : Fin 126) : Fin 126 := ⟨parentRows[i.val]!, parent_lt i⟩
private def edge (i : Fin 126) : Fin 2 := ⟨edgeRows[i.val]!, edge_lt i⟩

private theorem tree_edges : ∀ i : Fin 126, i ≠ 0 →
    depth (predecessor i) < depth i ∧ image (edge i) (predecessor i) = i := by
  decide +kernel

/-- Every point is reachable from zero using the exact two table images. -/
theorem table_image_induction (P : Fin 126 → Prop) (hzero : P 0)
    (hstep : ∀ j i, P i → P (image j i)) (i : Fin 126) : P i := by
  suffices ∀ n k, depth k = n → P k from this (depth i) i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro k hk
    by_cases hzero' : k = 0
    · simpa only [hzero'] using hzero
    · have ht := tree_edges k hzero'
      rw [← ht.2]
      apply hstep
      exact ih (depth (predecessor k)) (by omega) (predecessor k) rfl

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors.Realization
