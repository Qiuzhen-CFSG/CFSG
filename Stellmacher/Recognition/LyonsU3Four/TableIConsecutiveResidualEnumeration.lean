module

public import Stellmacher.Recognition.LyonsU3Four.TableIConsecutiveResidualData

/-!
# Exhaustiveness of the residual Case 5 counts

The seven residual Gram equations and the positive principal multiplicity
force exactly the four count vectors H, J, K, and L. Two nonnegative sums
first exclude the large orbit types. A linear combination of the Gram
equations then says that exactly one of counts 5, 9, 14, 17, and 20 is one.
The first and last possibilities are impossible; the middle three give H,
J, and the two possibilities K/L, respectively. All 23 multiplicities are
retained in the resulting equality of count functions.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 379,
Case 5(a)–(c). The candidate J is the corrected one in the data module.
-/

@[expose] public section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData.ConsecutiveResidual
set_option maxHeartbeats 2000000 in
/-- The residual Gram equations, with a positive principal count, have
exactly the four listed solutions, including all repeated rows. -/
theorem count_solutions (n : Fin 23 → ℕ) (h : CountConstraints n) : ∃ c : Fin 4, n = counts c := by
  have h00 := h.gram_eq 0 0
  have h01 := h.gram_eq 0 1
  have h02 := h.gram_eq 0 2
  have h11 := h.gram_eq 1 1
  have h12 := h.gram_eq 1 2
  have h22 := h.gram_eq 2 2
  have h23 := h.gram_eq 2 3
  simp [gram, rows, orbit, gramTarget, Fin.sum_univ_succ] at h00 h01 h02 h11 h12 h22 h23
  have hp := h.principal_pos
  -- The alternating orbits contribute exactly two pairs of rows.
  have hsum : n 0+n 2+n 3+n 7+n 8+n 11+n 13+n 16+n 19+n 21 = 2 := by linarith [h22, h23]
  -- The principal count consumes part of this nonnegative budget of four.
  have he : (4:ℤ) * n 0 + 4 * n 1 + n 4 + n 5 + n 6 + n 12 + 4 * n 13 + n 14 + n 15 + n 20 = 4 := by
    linarith [h11, h12, h23]
  have hz1 : n 0 = 0 ∧ n 1 = 0 ∧ n 13 = 0 := by
    clear h h00 h01 h02 h11 h12 h22 h23 hsum
    omega
  have hz2 : n 8 = 0 := by
    clear h h01 h02 h11 h12 h22 h23 hsum he hz1
    omega
  have hz3 : n 19 = 0 ∧ n 21 = 0 ∧ n 22 = 0 := by
    clear h h00 h01 h02 h11 h12 h22 hsum he hz1 hz2
    omega
  -- This integral identity leaves only five branches.
  have hf : n 5 + n 9 + n 14 + n 17 + n 20 + n 22 = 1 := by
    linarith only [h00, h01, h02, h11, h12, h22, h23]
  have hf' : n 5 = 1 ∨ n 9 = 1 ∨ n 14 = 1 ∨ n 17 = 1 ∨ n 20 = 1 := by
    clear h h00 h01 h02 h11 h12 h22 h23 hsum he hz1 hz2
    omega
  rcases hz1 with ⟨hz0, hz1, hz13⟩
  rcases hz3 with ⟨hz19, hz21, hz22⟩
  simp only [hz0, hz1, hz13, hz19, hz21, hz22, hz2, Nat.cast_zero,
    zero_add, add_zero, zero_mul, neg_zero] at h00 h01 h02 h11 h12 h22 h23 he hf hsum
  have hplus : (n 6 : ℤ) + n 10 + n 12 + 4 * n 15 + 4 * n 18 = 4 - 4 * n 2 - 4 * n 3 - 3 * n 5 - 3 * n 9 + n 20 := by
    linarith only [h00, h01]
  have hz4 : n 15 = 0 ∧ n 18 = 0 := by
    clear h h00 h01 h02 h12 h22 h23 he hsum
    omega
  rcases hz4 with ⟨hz15, hz18⟩
  simp only [hz15, hz18, Nat.cast_zero, zero_add, add_zero, zero_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
  clear h
  rcases hf' with h5 | h9 | h14 | h17 | h20
  · have hz : n 9 = 0 ∧ n 14 = 0 ∧ n 17 = 0 ∧ n 20 = 0 := by
      clear h00 h01 h02 h11 h12 h22 h23 he hp hsum
      omega
    rcases hz with ⟨z9, z14, z17, z20⟩
    simp only [z9, z14, z17, z20, h5, Nat.cast_zero, Nat.cast_one, zero_add, add_zero, zero_mul, neg_zero,
      one_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
    exfalso
    omega
  · have hz : n 5 = 0 ∧ n 14 = 0 ∧ n 17 = 0 ∧ n 20 = 0 := by
      clear h00 h01 h02 h11 h12 h22 h23 he hp hsum
      omega
    rcases hz with ⟨z5, z14, z17, z20⟩
    simp only [z5, z14, z17, z20, h9, Nat.cast_zero, Nat.cast_one, zero_add, add_zero, zero_mul, neg_zero,
      one_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
    refine ⟨0, ?_⟩
    funext i
    fin_cases i
    · change n 0 = 0
      omega
    · change n 1 = 0
      omega
    · change n 2 = 0
      omega
    · change n 3 = 0
      omega
    · change n 4 = 3
      omega
    · change n 5 = 0
      omega
    · change n 6 = 1
      omega
    · change n 7 = 1
      omega
    · change n 8 = 0
      omega
    · change n 9 = 1
      omega
    · change n 10 = 0
      omega
    · change n 11 = 0
      omega
    · change n 12 = 0
      omega
    · change n 13 = 0
      omega
    · change n 14 = 0
      omega
    · change n 15 = 0
      omega
    · change n 16 = 1
      omega
    · change n 17 = 0
      omega
    · change n 18 = 0
      omega
    · change n 19 = 0
      omega
    · change n 20 = 0
      omega
    · change n 21 = 0
      omega
    · change n 22 = 0
      omega
  · have hz : n 5 = 0 ∧ n 9 = 0 ∧ n 17 = 0 ∧ n 20 = 0 := by
      clear h00 h01 h02 h11 h12 h22 h23 he hp hsum
      omega
    rcases hz with ⟨z5, z9, z17, z20⟩
    simp only [z5, z9, z17, z20, h14, Nat.cast_zero, Nat.cast_one, zero_add, add_zero, zero_mul, neg_zero,
      one_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
    refine ⟨1, ?_⟩
    funext i
    fin_cases i
    · change n 0 = 0
      omega
    · change n 1 = 0
      omega
    · change n 2 = 0
      omega
    · change n 3 = 0
      omega
    · change n 4 = 1
      omega
    · change n 5 = 0
      omega
    · change n 6 = 2
      omega
    · change n 7 = 1
      omega
    · change n 8 = 0
      omega
    · change n 9 = 0
      omega
    · change n 10 = 2
      omega
    · change n 11 = 1
      omega
    · change n 12 = 0
      omega
    · change n 13 = 0
      omega
    · change n 14 = 1
      omega
    · change n 15 = 0
      omega
    · change n 16 = 0
      omega
    · change n 17 = 0
      omega
    · change n 18 = 0
      omega
    · change n 19 = 0
      omega
    · change n 20 = 0
      omega
    · change n 21 = 0
      omega
    · change n 22 = 0
      omega
  · have hz : n 5 = 0 ∧ n 9 = 0 ∧ n 14 = 0 ∧ n 20 = 0 := by
      clear h00 h01 h02 h11 h12 h22 h23 he hp hsum
      omega
    rcases hz with ⟨z5, z9, z14, z20⟩
    simp only [z5, z9, z14, z20, h17, Nat.cast_zero, Nat.cast_one, zero_add, add_zero, zero_mul, neg_zero,
      one_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
    have h12cases : n 12 = 0 ∨ n 12 = 1 := by omega
    rcases h12cases with hc | hc
    · refine ⟨3, ?_⟩
      funext i
      fin_cases i
      · change n 0 = 0
        omega
      · change n 1 = 0
        omega
      · change n 2 = 0
        omega
      · change n 3 = 0
        omega
      · change n 4 = 2
        omega
      · change n 5 = 0
        omega
      · change n 6 = 2
        omega
      · change n 7 = 2
        omega
      · change n 8 = 0
        omega
      · change n 9 = 0
        omega
      · change n 10 = 2
        omega
      · change n 11 = 0
        omega
      · change n 12 = 0
        omega
      · change n 13 = 0
        omega
      · change n 14 = 0
        omega
      · change n 15 = 0
        omega
      · change n 16 = 0
        omega
      · change n 17 = 1
        omega
      · change n 18 = 0
        omega
      · change n 19 = 0
        omega
      · change n 20 = 0
        omega
      · change n 21 = 0
        omega
      · change n 22 = 0
        omega
    · refine ⟨2, ?_⟩
      funext i
      fin_cases i
      · change n 0 = 0
        omega
      · change n 1 = 0
        omega
      · change n 2 = 0
        omega
      · change n 3 = 0
        omega
      · change n 4 = 0
        omega
      · change n 5 = 0
        omega
      · change n 6 = 3
        omega
      · change n 7 = 2
        omega
      · change n 8 = 0
        omega
      · change n 9 = 0
        omega
      · change n 10 = 0
        omega
      · change n 11 = 0
        omega
      · change n 12 = 1
        omega
      · change n 13 = 0
        omega
      · change n 14 = 0
        omega
      · change n 15 = 0
        omega
      · change n 16 = 0
        omega
      · change n 17 = 1
        omega
      · change n 18 = 0
        omega
      · change n 19 = 0
        omega
      · change n 20 = 0
        omega
      · change n 21 = 0
        omega
      · change n 22 = 0
        omega
  · have hz : n 5 = 0 ∧ n 9 = 0 ∧ n 14 = 0 ∧ n 17 = 0 := by
      clear h00 h01 h02 h11 h12 h22 h23 he hp hsum
      omega
    rcases hz with ⟨z5, z9, z14, z17⟩
    simp only [z5, z9, z14, z17, h20, Nat.cast_zero, Nat.cast_one, zero_add, add_zero, zero_mul, neg_zero,
      one_mul] at h00 h01 h02 h11 h12 h22 h23 he hsum
    exfalso
    omega
end Stellmacher.Recognition.LyonsU3Four.GeneralizedDecompositionData.ConsecutiveResidual
