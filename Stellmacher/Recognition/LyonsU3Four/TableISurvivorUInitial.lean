module
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorForcing
import Mathlib.Tactic

/-!
# The first signed degree of the Table I survivor U

The actual degree, order and prime constraints force the first signed degree
to be −13. Adding (U1) and (U3) first excludes degree −12 in the second
coordinate. If the first degree is not −13, (U2) restricts the fourth degree
to 39, 103 or 167. Schur's bound excludes the two large primes. Equation
(U1) then forces the fifth degree to be 170 and the first to be −77, whose
reciprocal equation contradicts the remaining degree gaps.

For the Schur step all nonprincipal representative rows are separated. The
sixth representative shares its decomposition entries with the principal row;
the actual degree lower bound supplies the missing separation.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
case (U), pp. 385–386; local source
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four.SurvivorU
private theorem separated {x : Fin 8 → ℤ}
    (hd : data.DegreeConstraints 0 (degree x)) (i : Fin 8) (hi : i ≠ 0) :
    data.RowSeparated (degree x) (representative i) := by
  have hn : representative i ≠ 0 := by fin_cases i <;> first | exact False.elim (hi rfl) | decide
  have hl := hd.degree_lower (representative i) hn
  intro k ε hε hr ht hz
  by_cases hk : k = 0
  · subst k
    have h0 : degree x 0 = 1 := hd.principal_degree
    rw [h0] at hr
    rcases sq_eq_one_iff.mp hε with rfl | rfl
    · simp only [one_mul] at hr
      rw [← hr] at hl
      norm_num at hl
    · have hh : degree x (representative i) = -1 := by linarith
      rw [hh] at hl
      norm_num at hl
  · clear hr
    fin_cases i <;> try exact False.elim (hi rfl)
    all_goals rcases sq_eq_one_iff.mp hε with rfl | rfl
    all_goals revert k; decide


private theorem not_large_prime {x : Fin 8 → ℤ} {g c e p : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g)
    (hpp : p.Prime) (hpl : 103 ≤ p) (hv : x 4 = p) : False := by
  have bounds (i : Fin 8) (hi : i ≠ 0) :
      (-1 / 102 : ℚ) ≤ (x i : ℚ)⁻¹ ∧ (x i : ℚ)⁻¹ ≤ 1 / 102 := by
    have hn : representative i ≠ 0 := by
      fin_cases i <;> first | exact False.elim (hi rfl) | decide
    have hl := hd.degree_lower (representative i) hn
    have hh := hp.prime_dvd_degree_le (by omega) (separated hd i hi)
      (representative 4) hpp (by simp only [degree_representative, hv, Int.natAbs_natCast, dvd_refl])
    simp only [degree_representative] at hh
    have hh' : (102 : ℤ) ≤ |x i| := by
      have : 102 ≤ (x i).natAbs := by omega
      simpa only [Int.natCast_natAbs, Nat.cast_ofNat] using (Int.ofNat_le.mpr this)
    have gap : x i ≤ -102 ∨ 102 ≤ x i := by
      rcases le_total (x i) 0 with hs | hs
      · rw [abs_of_nonpos hs] at hh'; omega
      · rw [abs_of_nonneg hs] at hh'; omega
    convert survivor_inv_bounds (by norm_num : (-102 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 102) gap using 1 <;> norm_num
  have b1 := bounds 1 (by decide)
  have b2 := bounds 2 (by decide)
  have b3 := bounds 3 (by decide)
  have b6 := bounds 6 (by decide)
  have b7 := bounds 7 (by decide)
  have gap4 : x 4 ≤ -25 ∨ 103 ≤ x 4 := by right; omega
  have b4 := (survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 103) gap4).2
  have he := (equations hd ho).h₂
  norm_num [div_eq_mul_inv] at he b4
  linarith only [he, b1.1, b2.1, b3.2, b6.1, b7.2, b4]

/-- The first signed degree in case U is forced by the actual constraints. -/
theorem x1_eq_neg_thirteen {x : Fin 8 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : x 1 = -13 := by
  have h1 := (equations hd ho).h₁
  have h2 := (equations hd ho).h₂
  have h3 := (equations hd ho).h₃
  have g1 : x 1 ≤ -13 ∨ 51 ≤ x 1 := degree_bounds hd 1 (by decide)
  have g2 : x 2 ≤ -12 ∨ 52 ≤ x 2 := degree_bounds hd 2 (by decide)
  have g3 : x 3 ≤ -63 ∨ 65 ≤ x 3 := degree_bounds hd 3 (by decide)
  have g4 : x 4 ≤ -25 ∨ 39 ≤ x 4 := degree_bounds hd 4 (by decide)
  have g5 : x 5 ≤ -150 ∨ 42 ≤ x 5 := degree_bounds hd 5 (by decide)
  have g6 : x 6 ≤ -63 ∨ 65 ≤ x 6 := degree_bounds hd 6 (by decide)
  have g7 : x 7 ≤ -12 ∨ 52 ≤ x 7 := degree_bounds hd 7 (by decide)
  have m1 : (x 1 - 51) % 64 = 0 := degree_mod hd 1
  have m2 : (x 2 + 12) % 64 = 0 := degree_mod hd 2
  have m4 : (x 4 - 39) % 64 = 0 := degree_mod hd 4
  have m5 : (x 5 + 150) % 64 = 0 := degree_mod hd 5
  have b1 := survivor_inv_bounds (by norm_num : (-13 : ℤ) < 0) (by norm_num : (0 : ℤ) < 51) g1
  have b3 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g3
  have b4 := survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0) (by norm_num : (0 : ℤ) < 39) g4
  have b6 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0) (by norm_num : (0 : ℤ) < 65) g6
  have b7 := survivor_inv_bounds (by norm_num : (-12 : ℤ) < 0) (by norm_num : (0 : ℤ) < 52) g7
  norm_num [div_eq_mul_inv] at h1 h2 h3 b1 b3 b4 b6 b7
  have n42 : x 5 ≠ 42 := by
    intro hv
    norm_num [hv] at h1
    linarith only [h1, b1.2, b3.1, b4.2, b6.1]
  -- The degree −12 would force a prime divisor 53 alongside degree 12.
  have n12 : x 2 ≠ -12 := by
    intro hv
    have v5 : x 5 = 106 := by
      by_contra hn
      have gap : x 5 ≤ -150 ∨ 170 ≤ x 5 := by omega
      have bb := (survivor_inv_bounds (by norm_num : (-150 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 170) gap).2
      norm_num [hv] at h3
      norm_num at bb
      linarith only [h1, h3, b3.2, b6.2, bb]
    have hh := prime_bound hd hp 2 (Or.inr (Or.inl rfl)) 5 53
      (by norm_num) (by rw [v5]; norm_num)
    norm_num [hv] at hh
  by_contra hn
  have g1' : x 1 ≤ -77 ∨ 51 ≤ x 1 := by omega
  have g2' : x 2 ≤ -76 ∨ 52 ≤ x 2 := by omega
  have b1' := survivor_inv_bounds (by norm_num : (-77 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 51) g1'
  have b2' := survivor_inv_bounds (by norm_num : (-76 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 52) g2'
  norm_num at b1' b2'
  -- The only positive fourth degrees allowed by (U2) are 39, 103 and 167.
  have v4 : x 4 = 39 := by
    have options : x 4 = 39 ∨ x 4 = 103 ∨ x 4 = 167 := by
      by_contra hh
      have gap : x 4 ≤ -25 ∨ 231 ≤ x 4 := by omega
      have bb := (survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 231) gap).2
      norm_num at bb
      linarith only [h2, b1'.1, b2'.1, b3.2, b6.1, b7.2, bb]
    rcases options with hh | hh | hh
    · exact hh
    · exact False.elim (not_large_prime hd ho hp (p := 103) (by norm_num) (by omega) hh)
    · exact False.elim (not_large_prime hd ho hp (p := 167) (by norm_num) (by omega) hh)
  have v5 : x 5 = 170 := by
    have n106 : x 5 ≠ 106 := by
      intro hv
      have hh := prime_bound hd hp 4 (Or.inr (Or.inr rfl)) 5 53
        (by norm_num) (by rw [hv]; norm_num)
      norm_num [v4] at hh
    by_contra hh
    have gap : x 5 ≤ -150 ∨ 234 ≤ x 5 := by omega
    have bb := (survivor_inv_bounds (by norm_num : (-150 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 234) gap).2
    norm_num [v4] at h1
    norm_num at bb
    linarith only [h1, b1'.1, b3.2, b6.2, bb]
  have v1 : x 1 = -77 := by
    by_contra hh
    have gap : x 1 ≤ -141 ∨ 51 ≤ x 1 := by omega
    have bb := (survivor_inv_bounds (by norm_num : (-141 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 51) gap).1
    norm_num [v4, v5] at h1
    norm_num at bb
    linarith only [h1, b3.2, b6.2, bb]
  norm_num [v1, v4, v5] at h1
  linarith only [h1, b3.1, b6.1]
end Stellmacher.Recognition.LyonsU3Four.SurvivorU
