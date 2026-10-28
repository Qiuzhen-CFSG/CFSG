/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianShortParity.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianParityIntegral

/-!
# IcosianShortParity

Every vector in the short-coordinate list satisfies the icosian parity
condition. Axis vectors reduce to zero and signed tetrads reduce to their
underlying codeword.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianShortParity.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

theorem icosianCoordinateSign_cast (b : Bit) :
    (icosianCoordinateSign b : Bit) = 1 := by
  by_cases h : b = 0 <;> simp [icosianCoordinateSign,h]

theorem icosianAxisCoordinates_parity (p : Fin 8 × Bit) :
    (fun j => (icosianAxisCoordinates p j : Bit)) ∈ icosianParity := by
  have h : (fun j => (icosianAxisCoordinates p j : Bit)) = 0 := by
    funext j
    by_cases hj : j = p.1 <;> simp [icosianAxisCoordinates,hj]
  rw [h]
  exact icosianParity.zero_mem

theorem icosianTetradCoordinates_cast (p : Fin 14 × (Fin 4 → Bit)) :
    (fun j => (icosianTetradCoordinates p j : Bit)) = icosianTetradWord p.1 := by
  classical
  funext j
  by_cases hj : ∃ i,icosianTetradPositions p.1 i = j
  · obtain ⟨i,rfl⟩ := hj
    rw [icosianTetradWord,if_pos ⟨i,rfl⟩]
    simp only [icosianTetradCoordinates,Int.cast_sum,Int.cast_ite,Int.cast_zero]
    rw [Finset.sum_eq_single i]
    · simp [icosianCoordinateSign_cast]
    · intro k hk hki
      have hne : icosianTetradPositions p.1 i ≠ icosianTetradPositions p.1 k :=
        fun h => hki ((icosianTetradPositions_injective p.1 h).symm)
      simp [hne]
    · simp
  · have hne : ∀ i,j ≠ icosianTetradPositions p.1 i := by
      intro i hi
      exact hj ⟨i,hi.symm⟩
    simp [icosianTetradCoordinates,icosianTetradWord,hj,hne]

theorem icosianShortCoordinates_parity (v : IcosianIntegerCoordinates)
    (hv : v ∈ icosianShortCoordinates) :
    (fun j => (v j : Bit)) ∈ icosianParity := by
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
    exact icosianAxisCoordinates_parity p
  · obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp h
    rw [icosianTetradCoordinates_cast]
    exact icosianTetradWord_mem p.1

end Atlas.Algebra
