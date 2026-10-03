module

public import Stellmacher.Recognition.LyonsU3Four.TableIJKLSystems
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

/-!
# Elimination of normalized Table I case J

Positivity and the signed degree gaps force the second printed degree to be
39 or 103. Schur's prime bound excludes 103. The linear equations and the
remaining reciprocal equation then force the first printed degree below -13;
the signed gap and the prime divisors 47, 41 and 269 improve this to at most
-333. Elementary reciprocal bounds force the last printed degree to be -76,
so the preceding degree is 1, contradicting its signed gap.

Source: R. Lyons, *A Characterization of the Group U₃(4)* (1972), p. 383,
case J (page images 383–384 checked in
`refs/original/n-group-global/odd-core-rank-two-source/lyons-u3four-1972-ams-wayback.pdf`).
We use the corrected matrix and normalized coordinates of `TableIJKLSystems`.
-/

public section
namespace Stellmacher.Recognition.LyonsU3Four.EarlyJ

local macro "ratlin" : tactic => `(tactic| (simp only [div_eq_mul_inv, one_mul] at *; linarith))

private theorem recip_bounds {x a b : ℤ} (ha : a < 0) (hb : 0 < b)
    (h : x ≤ a ∨ b ≤ x) : 1/(a:ℚ) ≤ 1/(x:ℚ) ∧ 1/(x:ℚ) ≤ 1/(b:ℚ) := by
  simp only [one_div]
  have ha' : (a : ℚ) < 0 := by exact_mod_cast ha
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  rcases h with h | h
  · have hx : (x : ℚ) ≤ a := by exact_mod_cast h
    have hn := hx.trans_lt ha'
    exact ⟨(inv_le_inv_of_neg ha' hn).mpr hx,
      (le_of_lt (inv_neg''.mpr hn)).trans (le_of_lt (inv_pos.mpr hb'))⟩
  · have hx : (b : ℚ) ≤ x := by exact_mod_cast h
    have hp := hb'.trans_le hx
    exact ⟨(le_of_lt (inv_neg''.mpr ha')).trans (le_of_lt (inv_pos.mpr hp)),
      (inv_le_inv₀ hp hb').mpr hx⟩

private theorem prime_transfer {x : Fin 9 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (hp : data.PrimeConstraints (degree x) g)
    (i j : Fin 9) (hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 8)
    (p : ℕ) (hpp : p.Prime) (hpd : p ∣ (x j).natAbs) :
    p ≤ (x i).natAbs + 1 :=
  prime_bound hd hp i hi p hpp (hpd.trans (degree_dvd hp j))

/-- The normalized degrees of Table I case J cannot satisfy the degree, order
and Schur prime constraints. -/
theorem impossible_normalized {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  obtain ⟨h1,h2,h3,hpos⟩ := equations hd ho
  have b2 := degree_bounds hd 2 (by decide)
  have b3 := degree_bounds hd 3 (by decide)
  have b4 := degree_bounds hd 4 (by decide)
  have b7 := degree_bounds hd 7 (by decide)
  have b8 := degree_bounds hd 8 (by decide)
  change x 2 ≤ -13 ∨ 51 ≤ x 2 at b2
  change x 3 ≤ -25 ∨ 39 ≤ x 3 at b3
  change x 4 ≤ -26 ∨ 102 ≤ x 4 at b4
  change x 7 ≤ -63 ∨ 65 ≤ x 7 at b7
  change x 8 ≤ -12 ∨ 52 ≤ x 8 at b8
  have m2 := degree_mod hd 2
  have m3 := degree_mod hd 3
  have m4 := degree_mod hd 4
  have m7 := degree_mod hd 7
  have m8 := degree_mod hd 8
  change (x 2 + -51) % 64 = 0 at m2
  change (x 3 + -39) % 64 = 0 at m3
  change (x 4 + -102) % 64 = 0 at m4
  change (x 7 + 63) % 64 = 0 at m7
  change (x 8 + 12) % 64 = 0 at m8
  obtain ⟨r7l,r7u⟩ := recip_bounds (by norm_num) (by norm_num) b7
  obtain ⟨r8l,r8u⟩ := recip_bounds (by norm_num) (by norm_num) b8
  norm_num at r7l r7u r8l r8u
  -- The positive weighted column leaves only two residues for the second degree.
  have v3 : x 3 = 39 ∨ x 3 = 103 := by
    by_contra hn
    have bb : x 3 ≤ -25 ∨ 167 ≤ x 3 := by omega
    have ru := (recip_bounds (by norm_num) (by norm_num) bb).2
    norm_num at ru
    ratlin
  have v3 : x 3 = 39 := by
    rcases v3 with hv | hv
    · exact hv
    exfalso
    have bound (i : Fin 9) (hi : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 7 ∨ i = 8) :
        103 ≤ (x i).natAbs + 1 :=
      prime_transfer hd hp i 3 hi 103 (by norm_num) (by norm_num [hv])
    have bb2 : x 2 ≤ -141 ∨ 115 ≤ x 2 := by have := bound 2 (by decide); omega
    have bb4 : x 4 ≤ -154 ∨ 102 ≤ x 4 := by have := bound 4 (by decide); omega
    have bb7 : x 7 ≤ -127 ∨ 129 ≤ x 7 := by have := bound 7 (by decide); omega
    have bb8 : x 8 ≤ -140 ∨ 116 ≤ x 8 := by have := bound 8 (by decide); omega
    have rr2 := (recip_bounds (by norm_num) (by norm_num) bb2).1
    have rr4 := (recip_bounds (by norm_num) (by norm_num) bb4).1
    have rr7 := (recip_bounds (by norm_num) (by norm_num) bb7).1
    have rr8 := (recip_bounds (by norm_num) (by norm_num) bb8).2
    norm_num [hv] at h1 rr2 rr4 rr7 rr8
    ratlin
  rw [v3] at h1 h2 h3
  norm_num at h1
  have neg2 : x 2 < -13 := by
    by_contra hn
    have cases2 : x 2 = -13 ∨ 51 ≤ x 2 := by omega
    rcases cases2 with hv | hv
    · have hv4 : x 4 = -26 := by omega
      norm_num [hv, hv4] at h1
      ratlin
    · have hv4 : x 4 ≤ -90 := by omega
      have a : (51:ℚ) ≤ x 2 := by exact_mod_cast hv
      have b : (x 4:ℚ) ≤ -90 := by exact_mod_cast hv4
      have s : (x 2:ℚ) + 39 + x 4 = 0 := by exact_mod_cast h3
      have ne2 : (x 2:ℚ) ≠ 0 := by linarith
      have ne4 : (x 4:ℚ) ≠ 0 := by linarith
      have hs : 9/(x 2:ℚ) + 36/(x 4:ℚ) ≤ 0 := by
        have eq : 9/(x 2:ℚ) + 36/(x 4:ℚ) =
            (9*(x 4:ℚ)+36*(x 2:ℚ))/((x 2:ℚ)*(x 4:ℚ)) := by
          field_simp
        rw [eq]
        apply div_nonpos_of_nonneg_of_nonpos
        · linarith
        · exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have v8 : x 8 = -12 := by
        by_contra hn8
        have bb : x 8 ≤ -76 ∨ 52 ≤ x 8 := by omega
        have rr := (recip_bounds (by norm_num) (by norm_num) bb).1
        norm_num at rr
        ratlin
      have rl4 := (recip_bounds (by norm_num : (-90:ℤ)<0)
        (by norm_num : (0:ℤ)<102) (Or.inl hv4)).1
      have r2 : (0:ℚ) ≤ 9/(x 2:ℚ) := div_nonneg (by norm_num) (by linarith)
      norm_num [v8] at h1 rl4
      ratlin
  -- J3 and the signed gap exclude -77; Schur excludes the next three residues.
  have small2 : x 2 ≤ -333 := by
    have ne141 : x 2 ≠ -141 := by
      intro hv
      have hh := prime_transfer hd hp 3 2 (by decide) 47 (by norm_num) (by norm_num [hv])
      norm_num [v3] at hh
    have ne205 : x 2 ≠ -205 := by
      intro hv
      have hh := prime_transfer hd hp 3 2 (by decide) 41 (by norm_num) (by norm_num [hv])
      norm_num [v3] at hh
    have ne269 : x 2 ≠ -269 := by
      intro hv
      have hh := prime_transfer hd hp 3 2 (by decide) 269 (by norm_num) (by norm_num [hv])
      norm_num [v3] at hh
    omega
  have large4 : 294 ≤ x 4 := by omega
  have r2l := (recip_bounds (by norm_num : (-333:ℤ)<0)
    (by norm_num : (0:ℤ)<51) (Or.inl small2)).1
  have r4u := (recip_bounds (by norm_num : (-26:ℤ)<0)
    (by norm_num : (0:ℤ)<294) (Or.inr large4)).2
  have r2n : 9/(x 2:ℚ) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num)
    (by exact_mod_cast (show x 2 ≤ 0 by omega))
  have r4p : 0 ≤ 36/(x 4:ℚ) := div_nonneg (by norm_num)
    (by exact_mod_cast (show 0 ≤ x 4 by omega))
  norm_num at r2l r4u
  -- Coarse reciprocal bounds suffice; no monotonicity calculation is needed.
  have v8 : x 8 = -76 := by
    have neg8 : x 8 < 0 := by
      have hr : 1/(x 8:ℚ) < 0 := by ratlin
      have hr' : (x 8:ℚ) < 0 := by simpa only [one_div, inv_neg''] using hr
      exact_mod_cast hr'
    have gt8 : -140 < x 8 := by
      by_contra hn
      have hh := (recip_bounds (by norm_num : (-140:ℤ)<0)
        (by norm_num : (0:ℤ)<52) (Or.inl (show x 8 ≤ -140 by omega))).1
      norm_num at hh
      ratlin
    have ne8 : x 8 ≠ -12 := by
      intro hv
      norm_num [hv] at h1
      ratlin
    omega
  omega

end Stellmacher.Recognition.LyonsU3Four.EarlyJ
