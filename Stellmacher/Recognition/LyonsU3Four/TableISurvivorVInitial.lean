module
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorForcing
import Mathlib.Tactic

/-!
# The first signed degree in survivor V

The actual degree, order, and prime constraints force `x 1 = -13`.
Adding the first equation to the positive third expression excludes
`x 2 = -12`: otherwise a middle degree must be 53, contradicting Schur's
bound from the separated degree-12 row. If `x 1 ≠ -13`, reciprocal bounds
in the second equation restrict `x 4` to 39, 103, or 167. The last two
values contradict the same equation after applying their prime bounds to
separated rows 1, 2, and 10. With `x 4 = 39`, the first equation again
forces a middle degree 53, contradicting the separated degree-39 bound.
The four middle degrees remain independent; their rows are never assumed
separated. The existing survivor completion supplies the remaining degrees.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972),
case (V), p. 386.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
open scoped BigOperators
namespace SurvivorV

private theorem last_row_separated (x : Fin 11 → ℤ) :
    data.RowSeparated (degree x) (representative 10) := by
  intro k ε he hr ht hz
  clear hr
  rcases sq_eq_one_iff.mp he with rfl | rfl
  all_goals revert k; decide

private theorem last_prime_bound {x : Fin 11 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (hp : data.PrimeConstraints (degree x) g) (k : Fin 11)
    (p : ℕ) (hpp : p.Prime) (hpk : p ∣ (x k).natAbs) :
    p ≤ (x 10).natAbs + 1 := by
  have hl := hd.degree_lower (representative 10) (by decide)
  have hh := hp.prime_dvd_degree_le (by omega) (last_row_separated x)
    (representative k) hpp (by simpa only [degree_representative] using hpk)
  simpa only [degree_representative] using hh

private theorem middle_gap {x : Fin 11 → ℤ}
    (hd : data.DegreeConstraints 0 (degree x)) (i : Fin 4)
    (hne : x (middleIndex i) ≠ 53) :
    x (middleIndex i) ≤ -75 ∨ 117 ≤ x (middleIndex i) := by
  have hb := degree_bounds hd (middleIndex i) (by fin_cases i <;> decide)
  have hm := degree_mod hd (middleIndex i)
  fin_cases i <;> norm_num [middleIndex, lower, upper, offset] at hb hm hne ⊢ <;> omega

private theorem middle_sum_bound {x : Fin 11 → ℤ}
    (hd : data.DegreeConstraints 0 (degree x))
    (hne : ∀ i, x (middleIndex i) ≠ 53) :
    (∑ i : Fin 4, 25 / (x (middleIndex i) : ℚ)) ≤ 100 / 117 := by
  have hb (i : Fin 4) := (survivor_inv_bounds (by norm_num : (-75 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 117) (middle_gap hd i (hne i))).2
  calc
    _ ≤ ∑ _i : Fin 4, (25 / 117 : ℚ) := by
      apply Finset.sum_le_sum
      intro i _
      have := hb i
      norm_num at this
      simp only [div_eq_mul_inv]
      linarith
    _ = _ := by norm_num

/-- The actual Table I constraints force the first signed degree in case V. -/
theorem x1_eq_neg_thirteen {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : x 1 = -13 := by
  have he := equations hd ho
  have g1 : x 1 ≤ -13 ∨ 51 ≤ x 1 := degree_bounds hd 1 (by decide)
  have g2 : x 2 ≤ -12 ∨ 52 ≤ x 2 := degree_bounds hd 2 (by decide)
  have g3 : x 3 ≤ -63 ∨ 65 ≤ x 3 := degree_bounds hd 3 (by decide)
  have g4 : x 4 ≤ -25 ∨ 39 ≤ x 4 := degree_bounds hd 4 (by decide)
  have g9 : x 9 ≤ -63 ∨ 65 ≤ x 9 := degree_bounds hd 9 (by decide)
  have g10 : x 10 ≤ -12 ∨ 52 ≤ x 10 := degree_bounds hd 10 (by decide)
  have m1 : (x 1 - 51) % 64 = 0 := degree_mod hd 1
  have m2 : (x 2 + 12) % 64 = 0 := degree_mod hd 2
  have m4 : (x 4 - 39) % 64 = 0 := degree_mod hd 4
  have m10 : (x 10 + 12) % 64 = 0 := degree_mod hd 10
  have b3 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 65) g3
  have b9 := survivor_inv_bounds (by norm_num : (-63 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 65) g9
  have b10 := survivor_inv_bounds (by norm_num : (-12 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 52) g10
  have n2 : x 2 ≠ -12 := by
    intro hx2
    have hn (i : Fin 4) : x (middleIndex i) ≠ 53 := by
      intro hm
      have hh := prime_bound hd hp 2 (Or.inr (Or.inl rfl)) (middleIndex i) 53
        (by norm_num) (by rw [hm]; norm_num)
      norm_num [hx2] at hh
    have hb := middle_sum_bound hd hn
    have h1 := he.h₁
    have h3 := he.h₃
    rw [hx2] at h3
    norm_num [div_eq_mul_inv] at h1 h3 hb b3 b9
    linarith
  by_contra hn1
  have gg1 : x 1 ≤ -77 ∨ 51 ≤ x 1 := by omega
  have gg2 : x 2 ≤ -76 ∨ 52 ≤ x 2 := by omega
  have b1 := survivor_inv_bounds (by norm_num : (-77 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 51) gg1
  have b2 := survivor_inv_bounds (by norm_num : (-76 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 52) gg2
  have v4 : x 4 = 39 ∨ x 4 = 103 ∨ x 4 = 167 := by
    by_contra hn
    have gg4 : x 4 ≤ -25 ∨ 231 ≤ x 4 := by omega
    have b4 := (survivor_inv_bounds (by norm_num : (-25 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 231) gg4).2
    have h2 := he.h₂
    norm_num [div_eq_mul_inv] at h2 b1 b2 b3 b4 b9 b10
    linarith
  have nlarge (hx4 : x 4 = 103 ∨ x 4 = 167) : False := by
    have hlarge : 102 ≤ (x 1).natAbs ∧ 102 ≤ (x 2).natAbs ∧
        102 ≤ (x 10).natAbs := by
      rcases hx4 with hx4 | hx4
      all_goals
        have hb1 := prime_bound hd hp 1 (Or.inl rfl) 4 _
          (by rw [hx4]; norm_num : (x 4).natAbs.Prime) (dvd_refl _)
        have hb2 := prime_bound hd hp 2 (Or.inr (Or.inl rfl)) 4 _
          (by rw [hx4]; norm_num : (x 4).natAbs.Prime) (dvd_refl _)
        have hb10 := last_prime_bound hd hp 4 _
          (by rw [hx4]; norm_num : (x 4).natAbs.Prime) (dvd_refl _)
        norm_num [hx4] at hb1 hb2 hb10
        omega
    have gl1 : x 1 ≤ -141 ∨ 115 ≤ x 1 := by omega
    have gl2 : x 2 ≤ -140 ∨ 116 ≤ x 2 := by omega
    have gl10 : x 10 ≤ -140 ∨ 116 ≤ x 10 := by omega
    have bl1 := survivor_inv_bounds (by norm_num : (-141 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 115) gl1
    have bl2 := survivor_inv_bounds (by norm_num : (-140 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 116) gl2
    have bl10 := survivor_inv_bounds (by norm_num : (-140 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 116) gl10
    have h2 := he.h₂
    rcases hx4 with hx4 | hx4
    all_goals
      rw [hx4] at h2
      norm_num [div_eq_mul_inv] at h2 bl1 bl2 bl10 b3 b9
      linarith
  have hx4 : x 4 = 39 := v4.resolve_right nlarge
  have hn (i : Fin 4) : x (middleIndex i) ≠ 53 := by
    intro hm
    have hh := prime_bound hd hp 4 (Or.inr (Or.inr rfl)) (middleIndex i) 53
      (by norm_num) (by rw [hm]; norm_num)
    norm_num [hx4] at hh
  have hb := middle_sum_bound hd hn
  have h1 := he.h₁
  rw [hx4] at h1
  norm_num [div_eq_mul_inv] at h1 hb b1 b3 b9
  linarith

end SurvivorV
end Stellmacher.Recognition.LyonsU3Four
