/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Algebra/IcosianCoordinateExhaustion.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Algebra.IcosianUnitCandidates

/-!
# IcosianCoordinateExhaustion

Every parity-allowed integer vector of squared length four occurs in
the short-coordinate list. The length bound leaves an axis vector or four
unit coordinates, and the parity-code classification determines the support.

Source: Gerald Höhn, ATLAS, `Atlas/Algebra/IcosianCoordinateExhaustion.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies.
-/

@[expose] public section

namespace Atlas.Algebra
open Atlas.Codes
open scoped BigOperators

theorem small_integer_bit_zero (z : ℤ) (hl : -1 ≤ z) (hu : z ≤ 1) :
    (z : Bit)=0 ↔ z=0 := by
  interval_cases z <;> decide

theorem small_integer_sign (z : ℤ) (hl : -1 ≤ z) (hu : z ≤ 1) (hz : z≠0) :
    icosianCoordinateSign (if z=1 then 0 else 1)=z := by
  interval_cases z <;> norm_num [icosianCoordinateSign] at *

/-- Exhaustion uses the squared-length bound and the actual sixteen-word
parity code; no norm-one list is assumed complete. -/
theorem icosianShortCoordinates_exhaust (v : IcosianIntegerCoordinates)
    (hn : icosianCoordinateNorm v=4)
    (hp : (fun j => (v j : Bit)) ∈ icosianParity) :
    v ∈ icosianShortCoordinates := by
  classical
  have hs : (∑ j,v j^2)=4 := hn
  have hb (j : Fin 8) : v j^2 ≤ 4 := by
    calc
      v j^2 ≤ ∑ k,v k^2 := Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
      _ = 4 := hs
  have hr (j : Fin 8) : -2 ≤ v j ∧ v j ≤ 2 := by
    have h := hb j
    constructor <;> nlinarith
  by_cases hlarge : ∃ j,v j=2 ∨ v j= -2
  · obtain ⟨j,hj⟩ := hlarge
    have hj2 : v j^2=4 := by rcases hj with h|h <;> rw [h] <;> norm_num
    have hz (k : Fin 8) (hkj : k≠j) : v k=0 := by
      have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin 8)) (fun i => v i^2) (Finset.mem_univ j)
      have hk : v k^2 ≤ ∑ i ∈ (Finset.univ : Finset (Fin 8)).erase j,v i^2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (v i)) (Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ k⟩)
      rw [hj2,hs] at hsum
      nlinarith [sq_nonneg (v k)]
    apply Finset.mem_union_left
    rcases hj with hj|hj
    · apply Finset.mem_image.mpr
      refine ⟨(j,0),Finset.mem_univ _,?_⟩
      funext k
      by_cases hk : k=j
      · subst k; simp [icosianAxisCoordinates,icosianCoordinateSign,hj]
      · simp [icosianAxisCoordinates,hk,hz k hk]
    · apply Finset.mem_image.mpr
      refine ⟨(j,1),Finset.mem_univ _,?_⟩
      funext k
      by_cases hk : k=j
      · subst k; norm_num [icosianAxisCoordinates,icosianCoordinateSign,hj]
      · simp [icosianAxisCoordinates,hk,hz k hk]
  · have hsmall (j : Fin 8) : -1 ≤ v j ∧ v j ≤ 1 := by
      have h := hr j
      have hnot : ¬(v j=2 ∨ v j= -2) := fun hj => hlarge ⟨j,hj⟩
      omega
    change ∃ a,icosianParityEncoder a=(fun j => (v j : Bit)) at hp
    obtain ⟨a,ha⟩ := hp
    rcases icosianParityEncoder_exhaust a with hzero|hone|⟨t,ht⟩
    · rw [ha] at hzero
      have hv : v=0 := by
        funext j
        apply (small_integer_bit_zero _ (hsmall j).1 (hsmall j).2).mp
        simpa using congrFun hzero j
      subst v
      norm_num [icosianCoordinateNorm] at hn
    · rw [ha] at hone
      have hv (j : Fin 8) : v j^2=1 := by
        have hcast := congrFun hone j
        have hl := (hsmall j).1
        have hu := (hsmall j).2
        have hz : v j≠0 := by intro hz; norm_num [hz] at hcast
        have htwo : v j= -1 ∨ v j=1 := by omega
        rcases htwo with h|h <;> rw [h] <;> norm_num
      simp_rw [hv] at hs
      norm_num at hs
    · rw [ha] at ht
      have houtside (j : Fin 8) (hj : ¬∃ i,icosianTetradPositions t i=j) : v j=0 := by
        apply (small_integer_bit_zero _ (hsmall j).1 (hsmall j).2).mp
        simpa [icosianTetradWord,hj] using congrFun ht j
      have hinside (i : Fin 4) : v (icosianTetradPositions t i)≠0 := by
        intro hz
        have hcast := congrFun ht (icosianTetradPositions t i)
        norm_num [hz,icosianTetradWord] at hcast
      let signs : Fin 4 → Bit := fun i => if v (icosianTetradPositions t i)=1 then 0 else 1
      have hsign (i : Fin 4) : icosianCoordinateSign (signs i)=v (icosianTetradPositions t i) :=
        small_integer_sign _ (hsmall _).1 (hsmall _).2 (hinside i)
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(t,signs),Finset.mem_univ _,?_⟩
      funext j
      by_cases hj : ∃ i,icosianTetradPositions t i=j
      · obtain ⟨i,rfl⟩ := hj
        rw [icosianTetradCoordinates,Finset.sum_eq_single i]
        · simp [hsign]
        · intro k _ hki
          have hne := (icosianTetradPositions_injective t).ne hki
          simp [Ne.symm hne]
        · simp
      · simp [icosianTetradCoordinates,houtside j hj,show ∀ i,j≠icosianTetradPositions t i from fun i h => hj ⟨i,h.symm⟩]

end Atlas.Algebra
