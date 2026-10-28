module

public import Mathlib.Data.Nat.Basic

/-!
# Numerical degree exclusions in G.9.3

These are the arithmetic consequences of the defining-characteristic degree
and automorphism-rank estimates on printed pp.356--357 of Aschbacher--Smith,
combined manuscript (1 March 2004). Lower degree estimates and rank bounds
remain explicit premises here; these lemmas do not assert them for a group.
The half-field parameter in the twisted SL₃ case is kept separate from the
group's field exponent. All inequalities retain the original actor rank.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.DegreeBounds

/-- Suzuki's faithful binary minimum contradicts the small-degree bound.
The standard Suzuki field exponent is odd and at least three. -/
theorem not_suzuki {d m n : ℕ} (hn : 3 ≤ n) (hm : m ≤ n)
    (hmin : 4 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- The unitary parameter is the fixed-field exponent: matrix entries lie
in the quadratic extension, accounting for binary degree `6*n`. -/
theorem not_unitary_three {d m n : ℕ} (hn : 2 ≤ n) (hm : m ≤ n + 1)
    (hmin : 6 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- The genuine triality binary minimum is `24*n`. -/
theorem not_triality {d m n : ℕ} (hn : 0 < n) (hm : m ≤ 5 * n)
    (hmin : 24 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- The Ree binary minimum is `26*n`; positivity also covers the smallest
parameter when the appropriate derived group is used. -/
theorem not_ree {d m n : ℕ} (hn : 0 < n) (hm : m ≤ 5 * n)
    (hmin : 26 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- Ordinary next-degree SL₃ modules are excluded. -/
theorem not_linear_three_next {d m n : ℕ} (hn : 0 < n) (hm : m ≤ 2 * n)
    (hmin : 8 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- In the twisted SL₃ case the group field has exponent `2*n`, so its
rank bound is `4*n`. The original actor has precisely this rank. -/
theorem linear_three_twisted_parameters {m n : ℕ} (_hn : 0 < n) (hm : m ≤ 4 * n)
    (hd : 9 * n ≤ 2 * (m + 1)) : n ≤ 2 ∧ m = 4 * n := by omega

/-- The smaller of the Sp₄ next-degree bounds is already too large for n≥2.
The derived group Sp₄(2)' requires its separate small-parameter analysis. -/
theorem not_symplectic_four_next {d m n : ℕ} (hn : 2 ≤ n) (hm : m ≤ 3 * n)
    (hmin : 8 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- The G₂ adjoint degree is already too large. -/
theorem not_g2_next {d m n : ℕ} (hn : 0 < n) (hm : m ≤ 3 * n)
    (hmin : 14 * n ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- PSL₄(2) has no room for its next degree fourteen. -/
theorem not_linear_four_next {d m : ℕ} (hm : m ≤ 4)
    (hmin : 14 ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

/-- PSL₅(2) has no room for its next degree twenty-four. -/
theorem not_linear_five_next {d m : ℕ} (hm : m ≤ 6)
    (hmin : 24 ≤ d) (hd : d ≤ 2 * (m + 1)) : False := by omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.DegreeBounds
