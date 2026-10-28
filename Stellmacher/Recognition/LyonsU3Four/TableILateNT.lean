module
public import Stellmacher.Recognition.LyonsU3Four.TableILateEquationData
import Mathlib.Tactic
/-!
# Prime-based eliminations of Table I cases N and T

The signed multiplicity gaps bound reciprocal degrees. In N exactly one
of the two offset-12 degrees is −12, giving row separation and Schur's
prime bound 13. Prime exclusions then force the contradictory degree 154.
In T the fourth degree is reduced to 39, 103, 167 or 231. Schur's prime
bounds and the reciprocal equations eliminate each possibility. Both proofs
retain multiplicity nonnegativity as well as the congruences modulo 64.

The last branch in T derives `x₆ < 0`; the repeated `x₆ > 0` on the
printed page is a sign error, as the preceding branch has just ruled it out.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, pp. 384–385.
-/
@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData
namespace LateN
theorem impossible {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  have h1 : LateSignedDegree (x 1) 63 := signed_degree hd 1 (by decide)
  have h2 : LateSignedDegree (x 2) 63 := signed_degree hd 2 (by decide)
  have h3 : LateSignedDegree (x 3) 12 := signed_degree hd 3 (by decide)
  have h4 : LateSignedDegree (x 4) 12 := signed_degree hd 4 (by decide)
  have h5 : LateSignedDegree (x 5) (-90) := signed_degree hd 5 (by decide)
  have h6 : LateSignedDegree (x 6) 63 := signed_degree hd 6 (by decide)
  have h7 : LateSignedDegree (x 7) 87 := signed_degree hd 7 (by decide)
  have h8 : LateSignedDegree (x 8) 63 := signed_degree hd 8 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBounds63
  obtain ⟨b2, b2'⟩ := h2.invBounds63
  obtain ⟨b3, b3'⟩ := h3.invBounds12
  obtain ⟨b4, b4'⟩ := h4.invBounds12
  obtain ⟨b5, b5'⟩ := h5.invBoundsneg90
  obtain ⟨b6, b6'⟩ := h6.invBounds63
  obtain ⟨b7, b7'⟩ := h7.invBounds87
  obtain ⟨b8, b8'⟩ := h8.invBounds63
  obtain ⟨n1, n2, _⟩ := equations hd ho
  simp only [lateCast, div_eq_mul_inv] at n1 n2
  change 1 + 4 * lateInv (x 1) + 4 * lateInv (x 2) - 200 * lateInv (x 5) +
    1 * lateInv (x 6) + 81 * lateInv (x 7) + 1 * lateInv (x 8) = 0 at n1
  change 2 + 3 * lateInv (x 1) + 3 * lateInv (x 2) + 16 * lateInv (x 3) +
    16 * lateInv (x 4) - 200 * lateInv (x 5) + 2 * lateInv (x 6) +
    2 * lateInv (x 8) = 0 at n2
  -- The exceptional positive degree would force the inconsistent degree 41.
  have ne5 : x 5 ≠ 90 := by
    intro hv
    have v7 : x 7 = 41 := by
      by_contra hn
      have hm := h7.integral
      have hg := h7.gap87
      change (x 7 + 87) % 64 = 0 % 64 at hm
      have hg' : x 7 ≤ -87 ∨ 105 ≤ x 7 := by omega
      have bb := (lateInv_bounds (by norm_num : (-87 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 105) hg').2
      norm_num [lateInv] at bb
      norm_num [hv, lateInv] at n1
      dsimp [lateInv] at *
      linarith
    norm_num [hv, v7, lateInv] at n1
    dsimp [lateInv] at *
    linarith
  have bg5 : x 5 ≤ -38 ∨ 154 ≤ x 5 := by
    have hm := h5.integral
    have hg := h5.gap_neg90
    change (x 5 + -90) % 64 = 0 % 64 at hm
    omega
  have bb5 := (lateInv_bounds (by norm_num : (-38 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 154) bg5).2
  norm_num [lateInv] at bb5
  change lateInv (x 5) ≤ _ at bb5
  -- Exactly one degree is −12, so its repeated-column block is separated.
  have hor : x 3 = -12 ∨ x 4 = -12 := by
    by_contra hn
    push Not at hn
    have bb3 := (h3.invBounds12_ne hn.1).1
    have bb4 := (h4.invBounds12_ne hn.2).1
    linarith
  have hne : x 3 ≠ x 4 := by
    intro he
    have v3 : x 3 = -12 := by rcases hor with h | h <;> omega
    have v4 : x 4 = -12 := by omega
    norm_num [v3, v4, lateInv] at n2
    dsimp [lateInv] at *
    linarith
  -- Schur now bounds every prime dividing any degree by 13.
  have bound (j : Fin 21) (p : ℕ) (hpp : p.Prime)
      (hpd : p ∣ (degree x j).natAbs) : p ≤ 13 := by
    rcases hor with hv | hv
    · have hs : 5 < (degree x 9).natAbs := by change 5 < (x 3).natAbs; norm_num [hv]
      have hh := hp.prime_dvd_degree_le hs (separated_left x hne) j hpp hpd
      change p ≤ (x 3).natAbs + 1 at hh
      simpa [hv] using hh
    · have hs : 5 < (degree x 13).natAbs := by change 5 < (x 4).natAbs; norm_num [hv]
      have hh := hp.prime_dvd_degree_le hs (separated_right x hne) j hpp hpd
      change p ≤ (x 4).natAbs + 1 at hh
      simpa [hv] using hh
  have ne76 (i : Fin 9) (hi : x i = -76) : False := by
    have hh := bound (representative i) 19 (by norm_num) (by
      have hrep : degree x (representative i) = x i := by fin_cases i <;> rfl
      rw [hrep, hi]; norm_num)
    omega
  have improved (i : Fin 9) (hi : LateSignedDegree (x i) 12) (hne : x i ≠ -12) :
      -1 / 140 ≤ lateInv (x i) := by
    have hn : x i ≠ -76 := fun h => ne76 i h
    have hm := hi.integral
    have hg := hi.gap12_ne hne
    change (x i + 12) % 64 = 0 % 64 at hm
    have hg' : x i ≤ -140 ∨ 52 ≤ x i := by omega
    have hh := (lateInv_bounds (by norm_num : (-140 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 52) hg').1
    simpa [lateInv, div_eq_mul_inv] using hh
  have v5 : x 5 = 154 := by
    by_contra hn
    have hg : x 5 ≤ -38 ∨ 600 ≤ x 5 := by
      by_contra hh
      have hm := h5.integral
      change (x 5 + -90) % 64 = 0 % 64 at hm
      have cases : x 5 = 218 ∨ x 5 = 282 ∨ x 5 = 346 ∨ x 5 = 410 ∨
          x 5 = 474 ∨ x 5 = 538 := by omega
      rcases cases with hv | hv | hv | hv | hv | hv
      all_goals
        have hb := bound 17
        change ∀ p : ℕ, p.Prime → p ∣ (x 5).natAbs → p ≤ 13 at hb
        norm_num [hv] at hb
      · have := hb 109 (by norm_num) (by norm_num); omega
      · have := hb 47 (by norm_num) (by norm_num); omega
      · have := hb 173 (by norm_num) (by norm_num); omega
      · have := hb 41 (by norm_num) (by norm_num); omega
      · have := hb 79 (by norm_num) (by norm_num); omega
      · have := hb 269 (by norm_num) (by norm_num); omega
    have bb := (lateInv_bounds (by norm_num : (-38 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 600) hg).2
    norm_num [lateInv] at bb
    change lateInv (x 5) ≤ _ at bb
    rcases hor with hv | hv
    · have hi := improved 4 h4 (by omega)
      norm_num [hv, lateInv] at n2
      dsimp [lateInv] at *
      linarith
    · have hi := improved 3 h3 (by omega)
      norm_num [hv, lateInv] at n2
      dsimp [lateInv] at *
      linarith
  rcases hor with hv | hv
  all_goals
    norm_num [hv, v5, lateInv] at n2
    dsimp [lateInv] at *
    linarith
end LateN

namespace LateT

/-- Transfer a prime divisor of one degree to a lower bound on any other
nonprincipal degree, using the separation of every T row. -/
private theorem prime_gap {x : Fin 7 → ℤ} {g : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (hp : data.PrimeConstraints (degree x) g)
    {p : ℕ} (hpp : p.Prime) (j : Fin 17) (hpd : p ∣ (degree x j).natAbs)
    (i : Fin 7) (hi : i ≠ 0) : p ≤ (x i).natAbs + 1 := by
  have hrep : degree x (representative i) = x i := by fin_cases i <;> rfl
  have hlo := (signed_degree hd i hi).lower
  have hs : 5 < (degree x (representative i)).natAbs := by rw [hrep]; omega
  simpa only [hrep] using
    hp.prime_dvd_degree_le hs (separated x (representative i)) j hpp hpd

theorem impossible {x : Fin 7 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  have h1 : LateSignedDegree (x 1) (-51) := signed_degree hd 1 (by decide)
  have h2 : LateSignedDegree (x 2) 12 := signed_degree hd 2 (by decide)
  have h3 : LateSignedDegree (x 3) 63 := signed_degree hd 3 (by decide)
  have h4 : LateSignedDegree (x 4) (-39) := signed_degree hd 4 (by decide)
  have h5 : LateSignedDegree (x 5) 87 := signed_degree hd 5 (by decide)
  have h6 : LateSignedDegree (x 6) 138 := signed_degree hd 6 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBoundsneg51
  obtain ⟨b2, b2'⟩ := h2.invBounds12
  obtain ⟨b3, b3'⟩ := h3.invBounds63
  obtain ⟨b4, b4'⟩ := h4.invBoundsneg39
  obtain ⟨b5, b5'⟩ := h5.invBounds87
  obtain ⟨b6, b6'⟩ := h6.invBounds138
  obtain ⟨t1, t2, t3, t4, _⟩ := equations hd ho
  simp only [lateCast, div_eq_mul_inv] at t1 t2 t4
  change 2 - 18 * lateInv (x 1) + 16 * lateInv (x 2) + 3 * lateInv (x 3) -
    147 * lateInv (x 4) + 108 * lateInv (x 6) = 0 at t1
  change 1 + 72 * lateInv (x 1) + 32 * lateInv (x 2) - 6 * lateInv (x 3) -
    243 * lateInv (x 5) = 0 at t2
  change 0 < 1 + 36 * lateInv (x 1) + 64 * lateInv (x 2) + 98 * lateInv (x 4) +
    81 * lateInv (x 5) + 72 * lateInv (x 6) at t4
  have t3i : 1 - 2 * x 4 - x 5 + x 6 = 0 := by
    dsimp [lateCast] at t3
    exact_mod_cast t3
  have ne2 : x 2 ≠ -12 := by
    intro hv
    have neg5 : x 5 < 0 := by
      have hh : lateInv (x 5) < 0 := by
        norm_num [hv, lateInv] at t2
        dsimp [lateInv] at *
        linarith
      have hh' : (x 5 : ℚ) < 0 := inv_neg''.mp hh
      exact_mod_cast hh'
    have inv5 : lateInv (x 5) < 0 := inv_neg''.mpr (by exact_mod_cast neg5)
    have v4 : x 4 = 39 := by
      by_contra hn
      have hm := h4.integral
      have hg := h4.gap_neg39
      change (x 4 + -39) % 64 = 0 % 64 at hm
      have hg' : x 4 ≤ -25 ∨ 103 ≤ x 4 := by omega
      have bb := (lateInv_bounds (by norm_num : (-25 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 103) hg').2
      norm_num [lateInv] at bb
      norm_num [hv, lateInv] at t4
      dsimp [lateInv] at *
      linarith
    have neg6 : x 6 < 0 := by have := h5.gap87; omega
    have inv6 : lateInv (x 6) < 0 := inv_neg''.mpr (by exact_mod_cast neg6)
    norm_num [hv, v4, lateInv] at t4
    dsimp [lateInv] at *
    linarith
  have ne1 : x 1 ≠ -13 := by
    intro hv
    norm_num [hv, lateInv] at t2
    dsimp [lateInv] at *
    linarith
  have bb2 := (h2.invBounds12_ne ne2).1
  have bb1 : -1 / 77 ≤ lateInv (x 1) := by
    have hm := h1.integral
    have hg := h1.gap_neg51
    change (x 1 + -51) % 64 = 0 % 64 at hm
    have hg' : x 1 ≤ -77 ∨ 51 ≤ x 1 := by omega
    simpa [lateInv, div_eq_mul_inv] using (lateInv_bounds
      (by norm_num : (-77 : ℤ) < 0) (by norm_num : (0 : ℤ) < 51) hg').1
  have pos4 : 0 < x 4 := by
    have hh : 0 < lateInv (x 4) := by linarith
    have hh' : (0 : ℚ) < x 4 := inv_pos.mp hh
    exact_mod_cast hh'
  have lt4 : x 4 < 295 := by
    by_contra hn
    have hh := (lateInv_bounds (by norm_num : (-25 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 295) (Or.inr (show 295 ≤ x 4 by omega))).2
    norm_num [lateInv] at hh
    dsimp [lateInv] at *
    linarith
  have cases4 : x 4 = 39 ∨ x 4 = 103 ∨ x 4 = 167 ∨ x 4 = 231 := by
    have hm := h4.integral
    change (x 4 + -39) % 64 = 0 % 64 at hm
    omega
  have ne39 : x 4 ≠ 39 := by
    intro hv
    have pos6 : 0 < x 6 := by
      have hh : 0 < lateInv (x 6) := by
        norm_num [hv, lateInv] at t1
        dsimp [lateInv] at *
        linarith
      have hh' : (0 : ℚ) < x 6 := inv_pos.mp hh
      exact_mod_cast hh'
    have lt6 : x 6 < 108 := by
      by_contra hn
      have hh := (lateInv_bounds (by norm_num : (-138 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 108) (Or.inr (show 108 ≤ x 6 by omega))).2
      norm_num [lateInv] at hh
      norm_num [hv, lateInv] at t1
      dsimp [lateInv] at *
      linarith
    have v6 : x 6 = 54 := by
      have hm := h6.integral
      change (x 6 + 138) % 64 = 0 % 64 at hm
      omega
    have := h5.gap87
    omega
  have ne167 : x 4 ≠ 167 := by
    intro hv
    have bound (i : Fin 7) (hi : i ≠ 0) : 167 ≤ (x i).natAbs + 1 :=
      prime_gap hd hp (by norm_num) 13 (by change 167 ∣ (x 4).natAbs; norm_num [hv]) i hi
    have invbound (i : Fin 7) (hi : i ≠ 0) :
        -1 / 166 ≤ lateInv (x i) ∧ lateInv (x i) ≤ 1 / 166 := by
      have hh := bound i hi
      have hg : x i ≤ -166 ∨ 166 ≤ x i := by omega
      simpa [lateInv, div_eq_mul_inv] using lateInv_bounds
        (by norm_num : (-166 : ℤ) < 0) (by norm_num : (0 : ℤ) < 166) hg
    have c1 := (invbound 1 (by decide)).2
    have c2 := (invbound 2 (by decide)).1
    have c3 := (invbound 3 (by decide)).1
    have c6 := (invbound 6 (by decide)).1
    norm_num [hv, lateInv] at t1
    dsimp [lateInv] at *
    linarith
  have ne231 : x 4 ≠ 231 := by
    intro hv
    have v6 : x 6 = -138 := by
      by_contra hn
      have hm := h6.integral
      have hg := h6.gap138
      change (x 6 + 138) % 64 = 0 % 64 at hm
      have hg' : x 6 ≤ -202 ∨ 54 ≤ x 6 := by omega
      have hh := (lateInv_bounds (by norm_num : (-202 : ℤ) < 0)
        (by norm_num : (0 : ℤ) < 54) hg').1
      norm_num [lateInv] at hh
      norm_num [hv, lateInv] at t1
      dsimp [lateInv] at *
      linarith
    have v5 : x 5 = -599 := by omega
    have hh := prime_gap hd hp (by norm_num : Nat.Prime 599) 15
      (by change 599 ∣ (x 5).natAbs; norm_num [v5]) 4 (by decide)
    norm_num [hv] at hh
  have v4 : x 4 = 103 := by omega
  have bound (i : Fin 7) (hi : i ≠ 0) : 103 ≤ (x i).natAbs + 1 :=
    prime_gap hd hp (by norm_num) 13 (by change 103 ∣ (x 4).natAbs; norm_num [v4]) i hi
  have invbound (i : Fin 7) (hi : i ≠ 0) :
      -1 / 102 ≤ lateInv (x i) ∧ lateInv (x i) ≤ 1 / 102 := by
    have hh := bound i hi
    have hg : x i ≤ -102 ∨ 102 ≤ x i := by omega
    simpa [lateInv, div_eq_mul_inv] using lateInv_bounds
      (by norm_num : (-102 : ℤ) < 0) (by norm_num : (0 : ℤ) < 102) hg
  -- This is the negative sign required by the closing argument on p. 385.
  have neg6 : x 6 < 0 := by
    by_contra hn
    have hh : 0 ≤ lateInv (x 6) := inv_nonneg.mpr (by exact_mod_cast (show 0 ≤ x 6 by omega))
    have c1 := (invbound 1 (by decide)).2
    have c2 := (invbound 2 (by decide)).1
    have c3 := (invbound 3 (by decide)).1
    norm_num [v4, lateInv] at t1
    dsimp [lateInv] at *
    linarith
  have neg5 : x 5 < 0 := by omega
  have inv5 : lateInv (x 5) < 0 := inv_neg''.mpr (by exact_mod_cast neg5)
  have c2 : -1 / 140 ≤ lateInv (x 2) := by
    have hh := bound 2 (by decide)
    have hm := h2.integral
    change (x 2 + 12) % 64 = 0 % 64 at hm
    have hg : x 2 ≤ -140 ∨ 52 ≤ x 2 := by omega
    simpa [lateInv, div_eq_mul_inv] using (lateInv_bounds
      (by norm_num : (-140 : ℤ) < 0) (by norm_num : (0 : ℤ) < 52) hg).1
  have c1 : -1 / 141 ≤ lateInv (x 1) := by
    have hh := bound 1 (by decide)
    have hm := h1.integral
    change (x 1 + -51) % 64 = 0 % 64 at hm
    have hg : x 1 ≤ -141 ∨ 51 ≤ x 1 := by omega
    simpa [lateInv, div_eq_mul_inv] using (lateInv_bounds
      (by norm_num : (-141 : ℤ) < 0) (by norm_num : (0 : ℤ) < 51) hg).1
  linarith
end LateT
end Stellmacher.Recognition.LyonsU3Four
