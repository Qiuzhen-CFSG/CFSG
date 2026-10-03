module

public import Stellmacher.Recognition.LyonsU3Four.TableILateBounds
import Mathlib.Tactic

/-!
# Eliminating the explicit matrices M, P, Q, R and S

For the signed degree labels printed in Table I, the actual matrix
`DegreeConstraints` and `OrderConstraints` are contradictory in cases
P, Q, R and S. Case M additionally uses `PrimeConstraints`, after proving
row separation for its degree-12 row. No arithmetic exclusion is assumed.

The finite weighted sums are computed in `TableILateMatrices`. The proofs
below use signed multiplicity bounds to restrict reciprocals, followed by
integer congruences and divisibility. In P the forced degrees are
`x₃ = x₄ = -76`, `x₉ = x₁₀ = 52`; the printed `-52, 76` is a transposition
inconsistent with both the matrix congruences and the following equation.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, pp. 384–385.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

namespace LateM

theorem separated (x : Fin 9 → ℤ) : data.RowSeparated (degree x) 13 := by
  intro k ε hε hdegree ht hz
  clear hdegree
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  all_goals revert k; decide

theorem impossible {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e)
    (hp : data.PrimeConstraints (degree x) g) : False := by
  obtain ⟨h0, _, hzw, _, _, _, _⟩ := constraints hd ho
  have h1 : LateSignedDegree (x 1) 63 := signed_degree hd 1 (by decide)
  have h2 : LateSignedDegree (x 2) 63 := signed_degree hd 2 (by decide)
  have h3 : LateSignedDegree (x 3) 63 := signed_degree hd 3 (by decide)
  have h4 : LateSignedDegree (x 4) 12 := signed_degree hd 4 (by decide)
  have h6 : LateSignedDegree (x 6) 63 := signed_degree hd 6 (by decide)
  have h7 : LateSignedDegree (x 7) 63 := signed_degree hd 7 (by decide)
  have h8 : LateSignedDegree (x 8) 12 := signed_degree hd 8 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBounds63
  obtain ⟨b2, b2'⟩ := h2.invBounds63
  obtain ⟨b3, b3'⟩ := h3.invBounds63
  obtain ⟨b6, b6'⟩ := h6.invBounds63
  obtain ⟨b7, b7'⟩ := h7.invBounds63
  obtain ⟨b8, b8'⟩ := h8.invBounds12
  simp only [zValue, wValue, h0, Int.cast_one, div_eq_mul_inv] at hzw
  have heq : 1 - lateInv (x 1) - lateInv (x 2) - lateInv (x 3) +
      16 * lateInv (x 4) + lateInv (x 6) + lateInv (x 7) -
      16 * lateInv (x 8) = 0 := by
    dsimp [lateInv]
    linarith
  have v4 : x 4 = -12 := by
    by_contra hn
    have b4 := (h4.invBounds12_ne hn).1
    linarith
  have v8 : x 8 ≠ -76 := by
    intro hv
    have hsmall : 5 < (degree x 13).natAbs := by
      change 5 < (x 4).natAbs
      norm_num [v4]
    have hdiv : 19 ∣ (degree x 20).natAbs := by
      change 19 ∣ (x 8).natAbs
      norm_num [hv]
    have hh := hp.prime_dvd_degree_le hsmall (separated x) 20 (by norm_num : Nat.Prime 19) hdiv
    change 19 ≤ (x 4).natAbs + 1 at hh
    norm_num [v4] at hh
  norm_num [v4, lateInv] at heq
  by_cases he : x 8 = -12
  · norm_num [he, lateInv] at heq
    dsimp [lateInv] at *
    linarith
  · have hm := h8.integral
    change (x 8 + 12) % 64 = 0 % 64 at hm
    have hl := h8.lower
    have hgap : x 8 ≤ -140 ∨ 52 ≤ x 8 := by omega
    have hb := (lateInv_bounds (by norm_num : (-140 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 52) hgap).1
    norm_num [lateInv] at hb
    dsimp [lateInv] at *
    linarith

end LateM

namespace LateP

private theorem inv_lower {a : ℤ} (h : LateSignedDegree a 63) (hn : a ≠ -63) :
    -1 / 127 ≤ lateInv a := by
  have hm := h.integral
  have hg := h.gap63
  change (a + 63) % 64 = 0 % 64 at hm
  have hh : a ≤ -127 ∨ 65 ≤ a := by omega
  have hb := (lateInv_bounds (by norm_num : (-127 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 65) hh).1
  simpa [lateInv, div_eq_mul_inv] using hb

private theorem inv_upper {a : ℤ} (h : LateSignedDegree a 63) (hn : a ≠ 65) :
    lateInv a ≤ 1 / 129 := by
  have hm := h.integral
  have hg := h.gap63
  change (a + 63) % 64 = 0 % 64 at hm
  have hh : a ≤ -63 ∨ 129 ≤ a := by omega
  have hb := (lateInv_bounds (by norm_num : (-63 : ℤ) < 0)
    (by norm_num : (0 : ℤ) < 129) hh).2
  simpa [lateInv] using hb

private theorem terminal_pair {a b : ℤ} (ha : LateSignedDegree a 63)
    (hb : LateSignedDegree b 63)
    (he : -1 / 63 + lateInv a - lateInv b = -9 / 247) : False := by
  have hor : a = -63 ∨ b = 65 := by
    by_contra hn
    push Not at hn
    have hla := inv_lower ha hn.1
    have hub := inv_upper hb hn.2
    linarith
  rcases hor with heq | heq
  · norm_num [heq, lateInv] at he
    have hn : (b : ℚ) ≠ 0 := by exact_mod_cast hb.nonzero
    have hq : (73 : ℚ) * b = 15561 := by
      field_simp [hn] at he
      linarith
    have hi : (73 : ℤ) * b = 15561 := by exact_mod_cast hq
    omega
  · norm_num [heq, lateInv] at he
    have hn : (a : ℚ) ≠ 0 := by exact_mod_cast ha.nonzero
    have hq : (31 : ℚ) * a = -5985 := by
      field_simp [hn] at he
      linarith
    have hi : (31 : ℤ) * a = -5985 := by exact_mod_cast hq
    omega

private theorem terminal {a b c : ℤ} (ha : LateSignedDegree a 63)
    (hb : LateSignedDegree b 63) (hc : LateSignedDegree c 63)
    (he : lateInv a + lateInv b - lateInv c = -9 / 247) : False := by
  have hor : a = -63 ∨ b = -63 := by
    by_contra hn
    push Not at hn
    have hla := inv_lower ha hn.1
    have hlb := inv_lower hb hn.2
    have huc := hc.invBounds63.2
    linarith
  rcases hor with heq | heq
  · apply terminal_pair hb hc
    simpa [heq, lateInv, div_eq_mul_inv] using he
  · apply terminal_pair ha hc
    norm_num [heq, lateInv] at he
    dsimp [lateInv]
    linarith

theorem impossible {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : False := by
  obtain ⟨h0, ht, hzw, hz, _, _, _⟩ := constraints hd ho
  have h1 : LateSignedDegree (x 1) 63 := signed_degree hd 1 (by decide)
  have h2 : LateSignedDegree (x 2) 63 := signed_degree hd 2 (by decide)
  have h3 : LateSignedDegree (x 3) 12 := signed_degree hd 3 (by decide)
  have h4 : LateSignedDegree (x 4) 12 := signed_degree hd 4 (by decide)
  have h5 : LateSignedDegree (x 5) (-90) := signed_degree hd 5 (by decide)
  have h6 : LateSignedDegree (x 6) 63 := signed_degree hd 6 (by decide)
  have h7 : LateSignedDegree (x 7) 75 := signed_degree hd 7 (by decide)
  have h8 : LateSignedDegree (x 8) 75 := signed_degree hd 8 (by decide)
  have h9 : LateSignedDegree (x 9) 12 := signed_degree hd 9 (by decide)
  have h10 : LateSignedDegree (x 10) 12 := signed_degree hd 10 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBounds63
  obtain ⟨b2, b2'⟩ := h2.invBounds63
  obtain ⟨b3, b3'⟩ := h3.invBounds12
  obtain ⟨b4, b4'⟩ := h4.invBounds12
  obtain ⟨b5, b5'⟩ := h5.invBoundsneg90
  obtain ⟨b6, b6'⟩ := h6.invBounds63
  obtain ⟨b7, b7'⟩ := h7.invBounds75
  obtain ⟨b8, b8'⟩ := h8.invBounds75
  obtain ⟨b9, b9'⟩ := h9.invBounds12
  obtain ⟨b10, b10'⟩ := h10.invBounds12
  simp only [tValue, zValue, wValue, h0, Int.cast_one, div_eq_mul_inv] at ht hzw hz
  have p1 : 1 + 4 * lateInv (x 1) + 4 * lateInv (x 2) - 200 * lateInv (x 5) +
      lateInv (x 6) + 25 * lateInv (x 7) + 25 * lateInv (x 8) = 0 := by
    dsimp [lateInv]
    linarith
  have p2 : 1 - lateInv (x 1) - lateInv (x 2) + 16 * lateInv (x 3) +
      16 * lateInv (x 4) + lateInv (x 6) - 16 * lateInv (x 9) -
      16 * lateInv (x 10) = 0 := by
    dsimp [lateInv]
    linarith
  have p3 : 0 < -4 * lateInv (x 1) - 4 * lateInv (x 2) +
      64 * lateInv (x 3) + 64 * lateInv (x 4) + 400 * lateInv (x 5) := by
    dsimp [lateInv]
    linarith
  have hx5 : 0 < x 5 := by
    have hh : 0 < lateInv (x 5) := by linarith
    have hh' : (0 : ℚ) < x 5 := inv_pos.mp hh
    exact_mod_cast hh'
  have hn5 : x 5 ≠ 90 := by
    intro he
    norm_num [he, lateInv] at p1
    dsimp [lateInv] at *
    linarith
  have h5lo : 154 ≤ x 5 := by
    have hm := h5.integral
    have hg := h5.gap_neg90
    change (x 5 + -90) % 64 = 0 % 64 at hm
    omega
  have b5new : lateInv (x 5) ≤ 1 / 154 := by
    have hh := (lateInv_bounds (by norm_num : (-38 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 154) (Or.inr h5lo)).2
    simpa [lateInv] using hh
  have ne3 : x 3 ≠ -12 := by
    intro he
    norm_num [he, lateInv] at p3
    dsimp [lateInv] at *
    linarith
  have ne4 : x 4 ≠ -12 := by
    intro he
    norm_num [he, lateInv] at p3
    dsimp [lateInv] at *
    linarith
  have b3new := (h3.invBounds12_ne ne3).1
  have b4new := (h4.invBounds12_ne ne4).1
  have stronger_neg (y : ℤ) (hy : LateSignedDegree y 12)
      (hn : y ≠ -12) (hn' : y ≠ -76) : -1 / 140 ≤ lateInv y := by
    have hm := hy.integral
    have hg := hy.gap12_ne hn
    change (y + 12) % 64 = 0 % 64 at hm
    have hh : y ≤ -140 ∨ 52 ≤ y := by omega
    have hi := (lateInv_bounds (by norm_num : (-140 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 52) hh).1
    simpa [lateInv, div_eq_mul_inv] using hi
  have v3 : x 3 = -76 := by
    by_contra hn
    have hh := stronger_neg _ h3 ne3 hn
    linarith
  have v4 : x 4 = -76 := by
    by_contra hn
    have hh := stronger_neg _ h4 ne4 hn
    linarith
  have stronger_pos (y : ℤ) (hy : LateSignedDegree y 12)
      (hn : y ≠ 52) : lateInv y ≤ 1 / 116 := by
    have hm := hy.integral
    have hg := hy.gap12
    change (y + 12) % 64 = 0 % 64 at hm
    have hh : y ≤ -12 ∨ 116 ≤ y := by omega
    have hi := (lateInv_bounds (by norm_num : (-12 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 116) hh).2
    simpa [lateInv] using hi
  have v9 : x 9 = 52 := by
    by_contra hn
    have hh := stronger_pos _ h9 hn
    linarith
  have v10 : x 10 = 52 := by
    by_contra hn
    have hh := stronger_pos _ h10 hn
    linarith
  apply terminal h1 h2 h6
  norm_num [v3, v4, v9, v10, lateInv] at p2
  dsimp [lateInv]
  linarith

end LateP

namespace LateR

private theorem terminal {a b : ℤ} (ha : LateSignedDegree a 63)
    (he : 4 * lateInv a + 25 * lateInv b = -7 / 33)
    (hl : 4 * a + b = 569) : False := by
  obtain ⟨ba, _⟩ := ha.invBounds63
  have hb : b < 0 := by
    by_contra hn
    have hi : 0 ≤ lateInv b := inv_nonneg.mpr (by exact_mod_cast (show 0 ≤ b by omega))
    linarith
  have hap : 0 < a := by omega
  have hia : 0 < lateInv a := inv_pos.mpr (by exact_mod_cast hap)
  have hb' : -165 < b := by
    by_contra hn
    have hh := (lateInv_bounds (by norm_num : (-165 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 1) (Or.inl (show b ≤ -165 by omega))).1
    norm_num [lateInv] at hh
    dsimp [lateInv] at *
    linarith
  have hm := ha.integral
  change (a + 63) % 64 = 0 % 64 at hm
  omega

theorem impossible {x : Fin 11 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : False := by
  obtain ⟨h0, ht, _, _, hi, _, _⟩ := constraints hd ho
  have h1 : LateSignedDegree (x 1) 63 := signed_degree hd 1 (by decide)
  have h5 : LateSignedDegree (x 5) (-165) := signed_degree hd 5 (by decide)
  have h6 : LateSignedDegree (x 6) 75 := signed_degree hd 6 (by decide)
  have h7 : LateSignedDegree (x 7) 75 := signed_degree hd 7 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBounds63
  obtain ⟨b5, b5'⟩ := h5.invBoundsneg165
  obtain ⟨b6, b6'⟩ := h6.invBounds75
  obtain ⟨b7, b7'⟩ := h7.invBounds75
  have heq : 1 + 4 * lateInv (x 1) - 75 * lateInv (x 5) +
      25 * lateInv (x 6) + 25 * lateInv (x 7) = 0 := by
    simpa [tValue, h0, lateInv, div_eq_mul_inv, sub_eq_add_neg] using ht
  have hlin : 1 + 4 * x 1 - 3 * x 5 + x 6 + x 7 = 0 := by
    simpa [tInner, h0, sub_eq_add_neg] using hi
  have hp5 : 0 < lateInv (x 5) := by linarith
  have hx5 : 0 < x 5 := by
    have : (0 : ℚ) < x 5 := inv_pos.mp hp5
    exact_mod_cast this
  have hone : 0 < x 1 ∨ 0 < x 6 ∨ 0 < x 7 := by omega
  have hb5 : (225 : ℚ)⁻¹ ≤ lateInv (x 5) := by
    rcases hone with h | h | h
    · have hh : 0 < lateInv (x 1) := inv_pos.mpr (by exact_mod_cast h)
      linarith
    · have hh : 0 < lateInv (x 6) := inv_pos.mpr (by exact_mod_cast h)
      linarith
    · have hh : 0 < lateInv (x 7) := inv_pos.mpr (by exact_mod_cast h)
      linarith
  have hub : x 5 ≤ 225 := by
    have hh : (x 5 : ℚ) ≤ 225 :=
      (inv_le_inv₀ (by norm_num : (0 : ℚ) < 225) (by exact_mod_cast hx5)).mp hb5
    exact_mod_cast hh
  have v5 : x 5 = 165 := by
    have hm := h5.integral
    have hg := h5.gap_neg165
    change (x 5 + -165) % 64 = 0 % 64 at hm
    omega
  have hor : x 6 = -75 ∨ x 7 = -75 := by
    by_contra hn
    push Not at hn
    have gap (y : ℤ) (hy : LateSignedDegree y 75) (hne : y ≠ -75) :
        y ≤ -139 ∨ 53 ≤ y := by
      have hm := hy.integral
      have hg := hy.gap75
      change (y + 75) % 64 = 0 % 64 at hm
      omega
    have bb6 := (lateInv_bounds (by norm_num : (-139 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 53) (gap _ h6 hn.1)).1
    have bb7 := (lateInv_bounds (by norm_num : (-139 : ℤ) < 0)
      (by norm_num : (0 : ℤ) < 53) (gap _ h7 hn.2)).1
    norm_num [lateInv, v5] at heq bb6 bb7
    dsimp [lateInv] at b1
    linarith
  rcases hor with hv | hv
  · apply terminal h1 (b := x 7)
    · norm_num [hv, v5, lateInv] at heq
      dsimp [lateInv]
      linarith
    · omega
  · apply terminal h1 (b := x 6)
    · norm_num [hv, v5, lateInv] at heq
      dsimp [lateInv]
      linarith
    · omega

end LateR


namespace LateS

theorem impossible {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : False := by
  obtain ⟨h0, ht, hzw, hz, _, _, _⟩ := constraints hd ho
  have h1 : LateSignedDegree (x 1) (-51) := signed_degree hd 1 (by decide)
  have h4 : LateSignedDegree (x 4) (-114) := signed_degree hd 4 (by decide)
  have h6 : LateSignedDegree (x 6) 75 := signed_degree hd 6 (by decide)
  have h7 : LateSignedDegree (x 7) 75 := signed_degree hd 7 (by decide)
  have h8 : LateSignedDegree (x 8) 12 := signed_degree hd 8 (by decide)
  obtain ⟨_, b1⟩ := h1.invBoundsneg51
  obtain ⟨_, b4⟩ := h4.invBoundsneg114
  obtain ⟨b6, _⟩ := h6.invBounds75
  obtain ⟨b7, _⟩ := h7.invBounds75
  obtain ⟨_, b8⟩ := h8.invBounds12
  simp only [tValue, zValue, wValue, h0, Int.cast_one,
    div_eq_mul_inv] at ht hzw hz
  dsimp [lateInv] at b1 b4 b6 b7 b8
  linarith

end LateS

namespace LateQ

theorem impossible {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) : False := by
  obtain ⟨h0, ht, hzw, hz, _, _, _⟩ := constraints hd ho
  have h1 : LateSignedDegree (x 1) 63 := signed_degree hd 1 (by decide)
  have h2 : LateSignedDegree (x 2) 12 := signed_degree hd 2 (by decide)
  have h3 : LateSignedDegree (x 3) 12 := signed_degree hd 3 (by decide)
  have h4 : LateSignedDegree (x 4) 12 := signed_degree hd 4 (by decide)
  have h5 : LateSignedDegree (x 5) (-165) := signed_degree hd 5 (by decide)
  have h7 : LateSignedDegree (x 7) 63 := signed_degree hd 7 (by decide)
  have h8 : LateSignedDegree (x 8) 12 := signed_degree hd 8 (by decide)
  obtain ⟨b1, b1'⟩ := h1.invBounds63
  obtain ⟨b2, b2'⟩ := h2.invBounds12
  obtain ⟨b3, b3'⟩ := h3.invBounds12
  obtain ⟨b4, b4'⟩ := h4.invBounds12
  obtain ⟨b5, b5'⟩ := h5.invBoundsneg165
  obtain ⟨b7, b7'⟩ := h7.invBounds63
  obtain ⟨b8, b8'⟩ := h8.invBounds12
  simp only [tValue, zValue, wValue, h0, Int.cast_one,
    div_eq_mul_inv] at ht hzw hz
  have q2 : 0 < -4 * lateInv (x 1) + 64 * lateInv (x 2) +
      64 * lateInv (x 3) + 64 * lateInv (x 4) + 100 * lateInv (x 5) := by
    dsimp [lateInv]
    linarith
  have ne2 : x 2 ≠ -12 := by
    intro he
    norm_num [he, lateInv] at q2
    dsimp [lateInv] at *
    linarith
  have ne3 : x 3 ≠ -12 := by
    intro he
    norm_num [he, lateInv] at q2
    dsimp [lateInv] at *
    linarith
  have ne4 : x 4 ≠ -12 := by
    intro he
    norm_num [he, lateInv] at q2
    dsimp [lateInv] at *
    linarith
  have c2 := (h2.invBounds12_ne ne2).1
  have c3 := (h3.invBounds12_ne ne3).1
  have c4 := (h4.invBounds12_ne ne4).1
  dsimp [lateInv] at *
  linarith

end LateQ


end Stellmacher.Recognition.LyonsU3Four
