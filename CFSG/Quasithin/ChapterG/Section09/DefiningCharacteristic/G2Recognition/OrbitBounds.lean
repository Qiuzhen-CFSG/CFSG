module

public import Mathlib.Algebra.BigOperators.Group.List.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Frobenius-block degree exclusions for G₂

For a nontrivial word in the basic degrees `1, 6, 14, 64`, its product `b`
is either six or at least fourteen. If a period of length `s` repeats `t`
times, Frobenius descent gives `n = s*t` and binary degree `d = s*b^t`.
For `t ≥ 2`, the inequality `14*t ≤ 6^t` excludes every repeated block.
Thus `d ≤ 6*n+2` forces `s=n`, `t=1` and one degree-six factor, with all
other factors trivial.

This is arithmetic on the dimensions from GLS3 2.8.10(g), including the
period repetition in 2.8.8. It neither assumes nor asserts a representation
classification: construction and exhaustivity of those basic modules, the
actual descent parameters, and identification of the six-dimensional factor
with the octonion quotient must be proved before applying these bounds to a
representation. Source: Aschbacher--Smith G.9.3, printed pp.356--357.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

/-- Arithmetic of products of the four basic G₂ degrees. -/
theorem basic_product_alternatives (l : List ℕ)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64) :
    l.prod = 1 ∨ l.prod = 6 ∨ 14 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have hb := ih (fun b hb => hl b (by simp [hb]))
    simp only [List.prod_cons]
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with hb | hb | hb
    all_goals omega

/-- A product of the four basic degrees equals six only when exactly one
factor is six and all the others are one. -/
theorem basic_product_eq_six (l : List ℕ)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64)
    (hprod : l.prod = 6) :
    ∃ l₁ l₂ : List ℕ, l = l₁ ++ 6 :: l₂ ∧
      (∀ a ∈ l₁, a = 1) ∧ (∀ a ∈ l₂, a = 1) := by
  induction l with
  | nil => simp at hprod
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht : ∀ b ∈ l, b = 1 ∨ b = 6 ∨ b = 14 ∨ b = 64 :=
      fun b hb => hl b (by simp [hb])
    have hp := basic_product_alternatives l ht
    simp only [List.prod_cons] at hprod
    rcases ha with rfl | rfl | rfl | rfl
    · obtain ⟨l₁, l₂, heq, h₁, h₂⟩ := ih ht (by simpa using hprod)
      refine ⟨1 :: l₁, l₂, by simp [heq], ?_, h₂⟩
      simpa using h₁
    · refine ⟨[], l, rfl, by simp, ?_⟩
      have hp1 : l.prod = 1 := by omega
      intro b hb
      have : b ∣ l.prod := List.dvd_prod hb
      rw [hp1] at this
      exact Nat.dvd_one.mp this
    · rcases hp with hp | hp | hp <;> omega
    · rcases hp with hp | hp | hp <;> omega

private theorem fourteen_mul_le_six_pow {t : ℕ} (ht : 2 ≤ t) :
    14 * t ≤ 6 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

/-- A repeated nontrivial block is at least as large as the adjoint bound. -/
theorem repeated_block_lower_bound {s t b : ℕ} (ht : 2 ≤ t) (hb : 6 ≤ b) :
    14 * (s * t) ≤ s * b ^ t := by
  have hp := (fourteen_mul_le_six_pow ht).trans (Nat.pow_le_pow_left hb t)
  calc
    14 * (s * t) = s * (14 * t) := by ring
    _ ≤ s * b ^ t := Nat.mul_le_mul_left s hp

/-- Once actual Frobenius descent supplies these parameters, the only
alternative below `14*n` is a single block of degree six. -/
theorem orbit_dimension_alternatives {s t b : ℕ} (ht : 0 < t)
    (hb : b = 6 ∨ 14 ≤ b) :
    (t = 1 ∧ b = 6) ∨ 14 * (s * t) ≤ s * b ^ t := by
  by_cases ht1 : t = 1
  · subst t
    rcases hb with rfl | hb
    · exact Or.inl ⟨rfl, rfl⟩
    · right
      simpa only [pow_one, mul_one, Nat.mul_comm] using Nat.mul_le_mul_left s hb
  · exact Or.inr (repeated_block_lower_bound (by omega) (by rcases hb with hb | hb <;> omega))

/-- The G.9 threshold forces a full-length period and a single degree-six block. -/
theorem small_orbit_parameters {n d s t b : ℕ} (hn : 0 < n)
    (ht : 0 < t) (hb : b = 6 ∨ 14 ≤ b)
    (hperiod : n = s * t) (hdim : d = s * b ^ t)
    (hsmall : d ≤ 6 * n + 2) : s = n ∧ t = 1 ∧ b = 6 ∧ d = 6 * n := by
  rcases orbit_dimension_alternatives ht hb with ⟨ht1, hb6⟩ | hlarge
  · subst t
    simp only [mul_one] at hperiod
    subst s
    subst b
    simp only [pow_one] at hdim
    exact ⟨rfl, rfl, rfl, by omega⟩
  · rw [← hperiod, ← hdim] at hlarge
    omega

/-- The complete numerical conclusion for a nontrivial basic-degree word.
The unique six-dimensional factor is located explicitly in the word. -/
theorem small_basic_block_parameters {n d s t : ℕ} (l : List ℕ)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64)
    (hnontrivial : l.prod ≠ 1) (hn : 0 < n) (ht : 0 < t)
    (hperiod : n = s * t) (hdim : d = s * l.prod ^ t)
    (hsmall : d ≤ 6 * n + 2) :
    s = n ∧ t = 1 ∧ d = 6 * n ∧
      ∃ l₁ l₂ : List ℕ, l = l₁ ++ 6 :: l₂ ∧
        (∀ a ∈ l₁, a = 1) ∧ (∀ a ∈ l₂, a = 1) := by
  have hb := (basic_product_alternatives l hl).resolve_left hnontrivial
  obtain ⟨hs, ht1, hb6, hd⟩ := small_orbit_parameters hn ht hb hperiod hdim hsmall
  exact ⟨hs, ht1, hd, basic_product_eq_six l hl hb6⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
