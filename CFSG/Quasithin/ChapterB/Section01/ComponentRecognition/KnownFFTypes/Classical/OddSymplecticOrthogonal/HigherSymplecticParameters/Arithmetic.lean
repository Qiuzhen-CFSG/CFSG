module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The numerical odd symplectic sieve

The projective degree estimate and the full-normalizer conjugate-generation
estimate give `q^r ≤ 2 * (2*r+1) * (2*r+2) + 1`. For odd `q ≥ 3` and
`r ≥ 2`, this leaves six parameter pairs. The exponential exceeds the
quadratic for every `r ≥ 6`; the remaining four ranks are bounded directly.

This is the numerical part of the odd symplectic branch of Guralnick–Malle,
*Classification of 2F-modules, I*, Proposition 4.5 (author manuscript p.13),
as used by Aschbacher–Smith B.1.13, printed pp.73–74. The representation
and automorphism estimates are separate hypotheses, not asserted here.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters

/-- Beyond rank five the least odd-field exponential exceeds the coarse bound. -/
theorem polynomial_lt_three_pow {r : ℕ} (hr : 6 ≤ r) :
    2 * (2 * r + 1) * (2 * r + 2) + 1 < 3 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

/-- The six pairs surviving the coarse cross-characteristic dimension comparison. -/
theorem candidates {r q : ℕ} (hr : 2 ≤ r) (hq : 3 ≤ q) (ho : Odd q)
    (hb : q ^ r ≤ 2 * (2 * r + 1) * (2 * r + 2) + 1) :
    (r = 2 ∧ (q = 3 ∨ q = 5 ∨ q = 7)) ∨ ((r = 3 ∨ r = 4 ∨ r = 5) ∧ q = 3) := by
  have hr5 : r ≤ 5 := by
    by_contra h
    have hlt := polynomial_lt_three_pow (by omega : 6 ≤ r)
    have hp : 3 ^ r ≤ q ^ r := Nat.pow_le_pow_left hq r
    omega
  obtain ⟨k, hk⟩ := ho
  interval_cases r
  · have hq7 : q ≤ 7 := by
      by_contra h
      have hp : 8 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
      norm_num at hb hp
      omega
    exact Or.inl ⟨rfl, by omega⟩
  · have hq4 : q ≤ 4 := by
      by_contra h
      have hp : 5 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
      norm_num at hb hp
      omega
    exact Or.inr ⟨by simp, by omega⟩
  · have hq3 : q ≤ 3 := by
      by_contra h
      have hp : 4 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left (by omega) 4
      norm_num at hb hp
      omega
    exact Or.inr ⟨by simp, by omega⟩
  · have hq3 : q ≤ 3 := by
      by_contra h
      have hp : 4 ^ 5 ≤ q ^ 5 := Nat.pow_le_pow_left (by omega) 5
      norm_num at hb hp
      omega
    exact Or.inr ⟨by simp, by omega⟩
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters
