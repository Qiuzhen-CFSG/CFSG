/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/OddMinimumOrthogonality.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.MinimalOddOrbit
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechShortShellCounts
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/OddMinimumOrthogonality.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem odd_base_no_constant_orthogonal_minimum (a : Omega) (x : IntegerCoordinates)
    (b : ℤ) (hb : ∀ i, i ≠ a → x i = b)
    (ho : integerDot (oddProfileBase {a} ∅) x = 0)
    (hn : integerDot x x = 32) : False := by
  have hcard : (Finset.univ.erase a).card = 23 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    decide
  have hs : (∑ i ∈ Finset.univ.erase a, x i) = 23*b := by
    rw [Finset.sum_congr rfl (fun i hi => hb i (Finset.mem_erase.mp hi).1)]
    simp [hcard]
  have hdot : integerDot (oddProfileBase {a} ∅) x = -3*x a + 23*b := by
    unfold integerDot
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)]
    have hr : (∑ i ∈ Finset.univ.erase a, oddProfileBase {a} ∅ i * x i) = 23*b := by
      rw [← hs]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := (Finset.mem_erase.mp hi).1
      simp [oddProfileBase,hi']
    rw [hr]
    simp [oddProfileBase]
  have hbound : x a * x a ≤ 32 := by
    rw [← hn]
    exact Finset.single_le_sum (fun i _ => mul_self_nonneg (x i)) (Finset.mem_univ a)
  have hxa : -5 ≤ x a ∧ x a ≤ 5 := by constructor <;> nlinarith
  have he : 3*x a = 23*b := by rw [hdot] at ho; omega
  have hb0 : b = 0 := by omega
  have ha0 : x a = 0 := by omega
  have hx0 : x = 0 := by
    funext i
    by_cases hi : i = a
    · simpa [hi] using ha0
    · simpa [hb0] using hb i hi
  simp [hx0,integerDot] at hn

end Atlas.Conway
