module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The degree arithmetic for the four basic symplectic modules

GLS volume 3, 2.8.10(d), lists the basic degrees 1, 4, 4, 16. A Frobenius
orbit with Schur degree s, repetition count t and a nontrivial factors in
each block therefore has binary degree s*(4^a)^t and field exponent s*t.
The next degree is at least 16n, except for one factor repeated twice,
which has degree 8n and requires even n.

This module proves only that numerical implication. Establishing these
parameters and recognizing the one-factor module require representation
theory; neither is a hypothesis of the source G.9.3 theorem.

Source: Aschbacher--Smith, G.9.3 proof, printed p.356, and
`refs/KGroup/GLS3/chapter2.tex`, Examples 2.8.10(d).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition

private theorem sixteen_mul_le_sixteen_pow {t : ℕ} (ht : 1 ≤ t) : 16 * t ≤ 16 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simp
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem sixteen_mul_le_four_pow {t : ℕ} (ht : 3 ≤ t) : 16 * t ≤ 4 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

/-- Degree gaps from the actual periodic-tensor parameter shape. The exceptional
half-field degree is retained separately, with its necessary parity. -/
theorem orbit_degree_alternatives {s t a n d : ℕ}
    (ht : 0 < t) (ha : 0 < a) (hn : n = s * t) (hd : d = s * (4 ^ a) ^ t) :
    (a = 1 ∧ t = 1) ∨ 16 * n ≤ d ∨ (Even n ∧ d = 8 * n) := by
  by_cases ha1 : a = 1
  · subst a
    by_cases ht1 : t = 1
    · exact Or.inl ⟨rfl, ht1⟩
    · by_cases ht2 : t = 2
      · right; right
        subst t
        refine ⟨⟨s, by omega⟩, ?_⟩
        simp only [pow_one] at hd
        norm_num at hd
        omega
      · right; left
        have hp := sixteen_mul_le_four_pow (by omega : 3 ≤ t)
        have hm := Nat.mul_le_mul_left s hp
        simp only [pow_one] at hd
        nlinarith
  · right; left
    have hb : 16 ≤ 4 ^ a := (by norm_num : 16 = 4 ^ 2) ▸
      Nat.pow_le_pow_right (by decide : 0 < 4) (by omega : 2 ≤ a)
    have hp := (sixteen_mul_le_sixteen_pow ht).trans (Nat.pow_le_pow_left hb t)
    have hm := Nat.mul_le_mul_left s hp
    nlinarith

/-- The G.9 degree window forces one nontrivial basic factor without repetition
when n≥2. The smallest derived group is intentionally outside this assertion. -/
theorem orbit_parameters_of_small_degree {s t a n d : ℕ}
    (ht : 0 < t) (ha : 0 < a) (hn : n = s * t) (hn2 : 2 ≤ n)
    (hd : d = s * (4 ^ a) ^ t) (hsmall : d ≤ 6 * n + 2) :
    a = 1 ∧ t = 1 ∧ s = n ∧ d = 4 * n := by
  rcases orbit_degree_alternatives ht ha hn hd with ⟨rfl, rfl⟩ | hlarge | ⟨_, hhalf⟩
  · simp only [pow_one, mul_one] at hn hd
    exact ⟨rfl, rfl, hn.symm, by omega⟩
  · omega
  · omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
