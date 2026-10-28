module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BlockArithmetic.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, public module boundaries, and Lean 4.33 proof adaptation.
-/

public import Mathlib.Tactic

/-! Divisibility of sums of the four subdegrees restricts the possible block sizes over every field size at least two. -/

@[expose] public section

namespace Atlas.G2

private theorem not_dvd_between_multiples {n d k : ℕ}
    (hlo : k*d < n) (hhi : n < (k+1)*d) : ¬ d ∣ n := by
  rintro ⟨m,rfl⟩
  have hm : k < m := by nlinarith
  nlinarith

/-- The middle suborbit alone cannot form a block with the base point. -/
theorem middle_block_not_dvd (q : ℕ) (hq : 2 ≤ q) :
    ¬ (1 + q^3*(q+1)) ∣ (q^5+q^4+q^3+q^2+q+1) := by
  apply not_dvd_between_multiples (k := q)
  · nlinarith [sq_nonneg (q:ℤ)]
  · have h2 : 1 < q^2 := by nlinarith
    have hh : q^2 < (q^2)^2 := by nlinarith
    have h : q^2 < q^4 := by simpa [← pow_mul] using hh
    nlinarith

/-- The union of the first three suborbits cannot be a proper block. -/
theorem first_three_block_not_dvd (q : ℕ) (hq : 2 ≤ q) :
    ¬ (1 + q*(q+1) + q^3*(q+1)) ∣ (q^5+q^4+q^3+q^2+q+1) := by
  apply not_dvd_between_multiples (k := q)
  · nlinarith
  · nlinarith

/-- Any block containing the open suborbit already exceeds half the degree. -/
theorem open_suborbit_more_than_half (q : ℕ) (hq : 2 ≤ q) :
    q^5+q^4+q^3+q^2+q+1 < 2*(1+q^5) := by
  have h : q*(q^4+q^3+q^2+q+1)+1 = q^5+(q^4+q^3+q^2+q+1) := by ring
  have hh := Nat.mul_le_mul_right (q^4+q^3+q^2+q+1) hq
  nlinarith

end Atlas.G2

namespace Atlas.G2
private theorem divisor_eq_of_large {s n : ℕ} (hd : s ∣ n)
    (hle : s ≤ n) (hlt : n < 2*s) : s = n := by
  obtain ⟨k,rfl⟩ := hd
  have hs : 0 < s := by nlinarith
  have hk0 : 0 < k := by nlinarith
  have hk2 : k < 2 := by nlinarith
  have hk : k=1 := by omega
  simp [hk]

def singularSubdegree (q : ℕ) : Fin 4 → ℕ := ![1,q*(q+1),q^3*(q+1),q^5]

theorem subdegree_block_candidates (q : ℕ) (hq : 2 ≤ q) (T : Finset (Fin 4))
    (hzero : 0 ∈ T)
    (hdiv : (∑ i ∈ T, singularSubdegree q i) ∣ q^5+q^4+q^3+q^2+q+1) :
    (∑ i ∈ T, singularSubdegree q i) = 1 ∨
    (∑ i ∈ T, singularSubdegree q i) = 1+q*(q+1) ∨
    (∑ i ∈ T, singularSubdegree q i) = q^5+q^4+q^3+q^2+q+1 := by
  classical
  have hm := middle_block_not_dvd q hq
  have ht := first_three_block_not_dvd q hq
  have ho := open_suborbit_more_than_half q hq
  fin_cases T <;> simp [singularSubdegree] at hzero hdiv ⊢
  all_goals first
    | exact False.elim (hm hdiv)
    | exact False.elim (ht (by simpa [Nat.add_assoc] using hdiv))
    | (have h := divisor_eq_of_large hdiv (by nlinarith) (by nlinarith); tauto)

end Atlas.G2

namespace Atlas.G2
/-- Only the base orbit, the candidate plane, or the entire point set can be a block. -/
theorem subdegree_block_index_candidates (q : ℕ) (hq : 2 ≤ q) (T : Finset (Fin 4))
    (hzero : 0 ∈ T)
    (hdiv : (∑ i ∈ T, singularSubdegree q i) ∣ q^5+q^4+q^3+q^2+q+1) :
    T = {0} ∨ T = {0,1} ∨ T = Finset.univ := by
  classical
  have hm := middle_block_not_dvd q hq
  have ht := first_three_block_not_dvd q hq
  have ho := open_suborbit_more_than_half q hq
  have hp3 : 0 < q^3 := pow_pos (by omega) _
  fin_cases T <;> simp [singularSubdegree] at hzero hdiv ⊢
  all_goals first
    | decide
    | exact False.elim (hm hdiv)
    | exact False.elim (ht (by simpa [Nat.add_assoc] using hdiv))
    | (have h := divisor_eq_of_large hdiv (by nlinarith) (by nlinarith); exfalso; nlinarith)
end Atlas.G2
