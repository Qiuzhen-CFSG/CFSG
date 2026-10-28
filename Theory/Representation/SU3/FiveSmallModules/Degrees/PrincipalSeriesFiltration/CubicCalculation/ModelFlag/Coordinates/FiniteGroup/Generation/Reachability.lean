module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.Coordinates.Certificate

/-!
# Reachability in the retained cubic coset table

A breadth-first spanning tree reaches all 126 indices from zero using the two
literal `generatorTarget` functions. Every edge and depth decrease is checked
by the kernel. The tree has maximum depth ten; its induction principle is
used with the actual matrix transitions in `Generation.lean`.

Source: `Coordinates/source/upper_group_data.json`; the reproduction script is
`Generation/source/emit_reachability.py`. This is the reachability part of the
SU₃(5) cubic certificate supporting Guralnick–Malle Proposition 4.3 and
Aschbacher–Smith K.2, printed p.453. No permutation-image generation assertion
is substituted for generation of the full special-unitary group.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup

private def depthRows : Array ℕ := #[0, 1, 4, 2, 6, 2, 6, 5, 3, 7, 3, 3, 6, 5, 6, 7, 5, 5, 8, 3, 6, 7, 4, 6, 5, 6, 8, 8, 6, 7, 6, 4, 9, 7, 8, 5, 8, 8, 6, 5, 4, 4, 7, 8, 4, 8, 8, 7, 5, 7, 8, 8, 6, 7, 8, 6, 9, 6, 7, 4, 7, 6, 7, 9, 4, 7, 5, 6, 7, 7, 6, 8, 5, 5, 7, 7, 9, 6, 8, 9, 8, 7, 9, 8, 7, 8, 7, 7, 8, 7, 8, 8, 9, 8, 9, 9, 9, 7, 8, 5, 7, 7, 5, 7, 6, 6, 6, 7, 6, 9, 9, 8, 6, 8, 7, 7, 10, 7, 6, 8, 6, 8, 5, 6, 9, 7]
private def parentRows : Array ℕ := #[0, 0, 8, 1, 16, 1, 24, 31, 5, 38, 3, 3, 48, 31, 24, 4, 59, 41, 62, 5, 66, 70, 11, 17, 40, 13, 69, 81, 7, 77, 7, 8, 88, 70, 74, 59, 9, 9, 13, 40, 10, 10, 106, 60, 11, 74, 107, 12, 44, 67, 115, 87, 39, 14, 89, 72, 43, 16, 28, 19, 104, 17, 105, 85, 19, 28, 44, 99, 77, 120, 122, 42, 22, 22, 23, 23, 91, 35, 29, 85, 68, 112, 27, 114, 118, 60, 30, 55, 125, 38, 125, 89, 78, 103, 83, 91, 51, 52, 53, 64, 120, 123, 41, 61, 102, 73, 102, 118, 122, 121, 90, 47, 72, 49, 57, 67, 79, 106, 99, 62, 66, 117, 64, 73, 98, 104]
private def edgeRows : Array ℕ := #[0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1]

private def depth (i : Fin 126) : ℕ := depthRows[i.val]!
private theorem parent_lt : ∀ i : Fin 126, parentRows[i.val]! < 126 := by decide +kernel
private theorem edge_lt : ∀ i : Fin 126, edgeRows[i.val]! < 2 := by decide +kernel
private def predecessor (i : Fin 126) : Fin 126 := ⟨parentRows[i.val]!, parent_lt i⟩
private def edge (i : Fin 126) : Fin 2 := ⟨edgeRows[i.val]!, edge_lt i⟩
private theorem tree_edges : ∀ i : Fin 126, i ≠ 0 →
    depth (predecessor i) < depth i ∧ generatorTarget (edge i) (predecessor i) = i := by
  decide +kernel

/-- Induction over the exact two retained transitions reaches every index from zero. -/
theorem generatorTarget_induction (P : Fin 126 → Prop) (hzero : P 0)
    (hstep : ∀ a i, P i → P (generatorTarget a i)) (i : Fin 126) : P i := by
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

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag.FiniteGroup
