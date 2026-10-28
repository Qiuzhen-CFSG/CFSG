module

public import Stellmacher.Recognition.LyonsU3Four.TableILateBounds
import Mathlib.Tactic

/-!
# Equation interfaces for the late Table I eliminations

These preserve the signed equation interfaces used by `TableIEliminationLate`.
For cases N and T, `LateN.equations` and `LateT.equations` derive the equations
and nonzero denominators from the explicit matrices and the original degree
and order constraints. The remaining N/T arithmetic can import this module
without depending on the final elimination assembly.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, pp. 384–385.
The M coefficients and the closing sign in T have been checked against the
page images and the actual weighted sums.
-/

@[expose] public section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

abbrev LateRational := ℚ

def lateCast (x : ℤ) : LateRational := x

/-! The equations as printed in the paper.  We keep the variables separate
because repeated rows in Table I still have distinct signed degrees. -/

/-- In this legacy seven-variable interface, the parameter `y₁` denotes the
paper's `y₄`; the actual table's `y₁` cancels from this equation. The
coefficients of `1/x₁` and `1/x₃` are one, as the page image and weighted
column calculation both confirm. -/
structure MEquations (x₁ x₂ x₃ x₄ y₁ y₂ y₃ : ℤ) : Prop where
  h₁ : 1 - 1 / lateCast x₁ - 1 / lateCast x₂ - 1 / lateCast x₃ + 16 / lateCast x₄ +
      1 / lateCast y₂ + 1 / lateCast y₃ - 16 / lateCast y₁ = 0
  nz : x₁ ≠ 0 ∧ x₂ ≠ 0 ∧ x₃ ≠ 0 ∧ x₄ ≠ 0 ∧ y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0

structure NEquations (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : ℤ) : Prop where
  h₁ : 1 + 4 / lateCast x₁ + 4 / lateCast x₂ - 200 / lateCast x₅ + 1 / lateCast x₆ +
      81 / lateCast x₇ + 1 / lateCast x₈ = 0
  h₂ : 2 + 3 / lateCast x₁ + 3 / lateCast x₂ + 16 / lateCast x₃ + 16 / lateCast x₄ -
      200 / lateCast x₅ + 2 / lateCast x₆ + 2 / lateCast x₈ = 0
  nz : ∀ i, lateCast (![x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈] i) ≠ 0

structure PEquations (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ x₁₀ : ℤ) : Prop where
  h₁ : 1 + 4 / lateCast x₁ + 4 / lateCast x₂ - 200 / lateCast x₅ + 1 / lateCast x₆ +
      25 / lateCast x₇ + 25 / lateCast x₈ = 0
  h₂ : 1 - 1 / lateCast x₁ - 1 / lateCast x₂ + 16 / lateCast x₃ + 16 / lateCast x₄ +
      1 / lateCast x₆ - 16 / lateCast x₉ - 16 / lateCast x₁₀ = 0
  h₃ : -4 / lateCast x₁ - 4 / lateCast x₂ + 64 / lateCast x₃ + 64 / lateCast x₄ +
      400 / lateCast x₅ > 0
  nz : ∀ i, lateCast (![x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈, x₉, x₁₀] i) ≠ 0

structure QEquations (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ : ℤ) : Prop where
  h₁ : 2 + 3 / lateCast x₁ + 16 / lateCast x₂ + 16 / lateCast x₃ + 16 / lateCast x₄ -
      75 / lateCast x₅ + 2 / lateCast x₇ - 16 / lateCast x₈ = 0
  h₂ : -4 / lateCast x₁ + 64 / lateCast x₂ + 64 / lateCast x₃ + 64 / lateCast x₄ +
      100 / lateCast x₅ > 0
  nz : ∀ i, lateCast (![x₁, x₂, x₃, x₄, x₅, x₆, x₇, x₈] i) ≠ 0

structure REquations (x₁ x₅ x₆ x₇ : ℤ) : Prop where
  h₁ : 1 + 4 / lateCast x₁ - 75 / lateCast x₅ + 25 / lateCast x₆ + 25 / lateCast x₇ = 0
  h₂ : 1 + 4 * lateCast x₁ - 3 * lateCast x₅ + lateCast x₆ + lateCast x₇ = 0
  nz : x₁ ≠ 0 ∧ x₅ ≠ 0 ∧ x₆ ≠ 0 ∧ x₇ ≠ 0

structure TEquations (x₁ x₂ x₃ x₄ x₅ x₆ : ℤ) : Prop where
  h₁ : 2 - 18 / lateCast x₁ + 16 / lateCast x₂ + 3 / lateCast x₃ -
      147 / lateCast x₄ + 108 / lateCast x₆ = 0
  h₂ : 1 + 72 / lateCast x₁ + 32 / lateCast x₂ - 6 / lateCast x₃ - 243 / lateCast x₅ = 0
  h₃ : 1 - 2 * lateCast x₄ - lateCast x₅ + lateCast x₆ = 0
  h₄ : 1 + 36 / lateCast x₁ + 64 / lateCast x₂ + 98 / lateCast x₄ +
      81 / lateCast x₅ + 72 / lateCast x₆ > 0
  nz : ∀ i, lateCast (![x₁, x₂, x₃, x₄, x₅, x₆] i) ≠ 0

/-! Matrix-derived equation interfaces for the remaining arithmetic work.
The closing T argument in the printed source repeats `x₆ > 0` after
contradicting that case. Its logically required conclusion is `x₆ < 0`;
no sign conclusion is assumed in the following bridge. -/

namespace LateN

theorem equations {x : Fin 9 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    NEquations (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) := by
  obtain ⟨h0, ht, hzw, _, _, _, _⟩ := constraints hd ho
  simp only [tValue, zValue, wValue, h0, Int.cast_one, div_eq_mul_inv] at ht hzw
  refine ⟨?_, ?_, ?_⟩
  · simp only [lateCast, div_eq_mul_inv]
    linarith
  · simp only [lateCast, div_eq_mul_inv]
    linarith
  · have hn (j : Fin 9) (hj : j ≠ 0) : lateCast (x j) ≠ 0 := by
      change (x j : ℚ) ≠ 0
      exact_mod_cast (signed_degree hd j hj).nonzero
    intro i
    fin_cases i
    · exact hn 1 (by decide)
    · exact hn 2 (by decide)
    · exact hn 3 (by decide)
    · exact hn 4 (by decide)
    · exact hn 5 (by decide)
    · exact hn 6 (by decide)
    · exact hn 7 (by decide)
    · exact hn 8 (by decide)

end LateN

namespace LateT

theorem equations {x : Fin 7 → ℤ} {g c e : ℕ}
    (hd : data.DegreeConstraints 0 (degree x))
    (ho : data.OrderConstraints (degree x) g c e) :
    TEquations (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) := by
  obtain ⟨h0, ht, hzw, hz, hit, hiz, hiw⟩ := constraints hd ho
  simp only [tValue, zValue, wValue, h0, Int.cast_one, div_eq_mul_inv] at ht hzw hz
  simp only [tInner, zInner, wInner, h0] at hit hiz hiw
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [lateCast, div_eq_mul_inv]
    linarith
  · simp only [lateCast, div_eq_mul_inv]
    linarith
  · have hh : 1 - 2 * x 4 - x 5 + x 6 = 0 := by linarith
    dsimp only [lateCast]
    exact_mod_cast hh
  · simp only [lateCast, div_eq_mul_inv]
    linarith
  · have hn (j : Fin 7) (hj : j ≠ 0) : lateCast (x j) ≠ 0 := by
      change (x j : ℚ) ≠ 0
      exact_mod_cast (signed_degree hd j hj).nonzero
    intro i
    fin_cases i
    · exact hn 1 (by decide)
    · exact hn 2 (by decide)
    · exact hn 3 (by decide)
    · exact hn 4 (by decide)
    · exact hn 5 (by decide)
    · exact hn 6 (by decide)

end LateT

/-! Row separation needed by the Schur bound. Every row in T is distinct
up to sign. In N the two `Z₆` blocks have equal columns, so their signed
degrees must first be distinguished. -/

namespace LateT

theorem separated (x : Fin 7 → ℤ) (j : Fin 17) :
    data.RowSeparated (degree x) j := by
  intro k ε hε hdegree ht hz
  clear hdegree
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  all_goals revert k; revert j; decide

end LateT
namespace LateN

theorem separated_left (x : Fin 9 → ℤ) (hne : x 3 ≠ x 4) :
    data.RowSeparated (degree x) 9 := by
  intro k ε hε hdegree ht hz
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul] at ht hz hdegree
    have hrows : ∀ k : Fin 21, data.dT k = data.dT 9 →
        (∀ i, data.iDz i k = data.iDz i 9) → k = 9 ∨ k = 13 := by decide
    rcases hrows k ht hz with rfl | rfl
    · rfl
    · exact False.elim (hne hdegree.symm)
  · clear hdegree
    revert k
    decide

theorem separated_right (x : Fin 9 → ℤ) (hne : x 3 ≠ x 4) :
    data.RowSeparated (degree x) 13 := by
  intro k ε hε hdegree ht hz
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · simp only [one_mul] at ht hz hdegree
    have hrows : ∀ k : Fin 21, data.dT k = data.dT 13 →
        (∀ i, data.iDz i k = data.iDz i 13) → k = 9 ∨ k = 13 := by decide
    rcases hrows k ht hz with rfl | rfl
    · exact False.elim (hne hdegree)
    · rfl
  · clear hdegree
    revert k
    decide

end LateN
end Stellmacher.Recognition.LyonsU3Four
