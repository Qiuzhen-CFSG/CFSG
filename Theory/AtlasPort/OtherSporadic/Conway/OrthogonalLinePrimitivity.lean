/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OrthogonalLinePrimitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLinePartition
public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-!
Primitivity of the norm-four vector stabilizer on orthogonal minimum lines.
The five suborbit sizes exclude a nontrivial block system.

Source: Gerald Höhn, `Atlas/Conway/OrthogonalLinePrimitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
set_option maxRecDepth 10000

theorem orthogonalLine_fiber_card (i j : Omega) (hij : i ≠ j) (t : Fin 5) :
    Nat.card {l : OrthogonalMinimumLines (minimumPairPlus i j) // orthogonalLineIndex i j l = t} =
      ![1,462,21120,2464,22528] t := by
  have h : Nonempty (OrthogonalClassType i j t) := (Nat.card_pos_iff.mp (by
    rw [orthogonalClass_card i j hij]; fin_cases t <;> decide)).1
  obtain ⟨x⟩ := h
  rw [Nat.card_congr (orthogonalLineFiberOrbitEquiv i j hij t x)]
  exact orthogonal_line_suborbit_card i j hij t x

theorem distinguishedOrthogonalLine_index (i j : Omega) (hij : i ≠ j) :
    orthogonalLineIndex i j (distinguishedOrthogonalLine i j hij) = 0 := by
  exact orthogonalClassLine_index i j hij 0 ⟨minimumPairMinus i j,Or.inl rfl⟩

theorem orthogonalMinimumLines_primitive (i j : Omega) (hij : i ≠ j) :
    MulAction.IsPreprimitive (fullVectorStabilizer (minimumPairPlus i j))
      (OrthogonalMinimumLines (minimumPairPlus i j)) := by
  let := orthogonalMinimumLines_pretransitive i j hij
  apply Atlas.GroupTheory.primitive_of_suborbit_sums (distinguishedOrthogonalLine i j hij)
    (orthogonalLineIndex i j) (orthogonalLine_index_transitive i j hij)
    (![1,462,21120,2464,22528]) (orthogonalLine_fiber_card i j hij)
  intro T hT hd
  rw [distinguishedOrthogonalLine_index] at hT
  rw [orthogonalMinimumLines_card i j hij] at hd ⊢
  have hc : ∀ S : Finset (Fin 5), 0 ∈ S →
      (∑ t ∈ S, (![1,462,21120,2464,22528] t : ℕ)) ∣ 46575 →
      (∑ t ∈ S, (![1,462,21120,2464,22528] t : ℕ)) = 1 ∨
      (∑ t ∈ S, (![1,462,21120,2464,22528] t : ℕ)) = 46575 := by decide
  exact hc T hT hd

end Atlas.Conway
