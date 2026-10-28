module

public import Mathlib.Tactic.Linarith

/-!
# The SL₃ tensor-orbit degree gap

The four binary restricted SL₃ factors have dimensions 1, 3, 3 and 8.
A block with `a` natural or dual factors and `b` adjoint factors has degree
`3^a * 8^b`. If a block of length `s` repeats `t` times, its binary orbit
degree is `s * (3^a * 8^b)^t`, while the group field exponent is `s*t`.

Apart from one natural factor repeated once or twice, this degree is at
least `8*s*t`. The G.9 bound excludes that gap and limits the double repeat
to `s ≤ 2`. This is a numerical theorem: the representation classification
and the identification of `s` with the Schur-field degree remain necessary.

Source: GLS III 2.8.6, 2.8.8, 2.8.10(c), and Aschbacher--Smith,
G.9.3, printed pp.354,356--357.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem eight_mul_le_pow {c t : ℕ} (hc : 8 ≤ c) (ht : 0 < t) :
    8 * t ≤ c ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hc
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

private theorem eight_mul_le_three_pow {t : ℕ} (ht : 3 ≤ t) : 8 * t ≤ 3 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

theorem orbit_degree_gap {s t a b : ℕ} (ht : 0 < t) (hab : 0 < a + b) :
    (a = 1 ∧ b = 0 ∧ t = 1) ∨ (a = 1 ∧ b = 0 ∧ t = 2) ∨
      8 * (s * t) ≤ s * (3 ^ a * 8 ^ b) ^ t := by
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 1
    · subst a
      rcases (by omega : t = 1 ∨ t = 2 ∨ 3 ≤ t) with ht1 | ht2 | ht3
      · exact Or.inl ⟨rfl, rfl, ht1⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, ht2⟩)
      · right; right
        simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_three_pow ht3)
    · have ha2 : 2 ≤ a := by omega
      have hp : 9 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) ha2
      right; right
      simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_pow (by omega : 8 ≤ 3 ^ a) ht)
  · have hb1 : 1 ≤ b := by omega
    have hp : 8 ≤ 8 ^ b := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb1
    have hapos : 1 ≤ 3 ^ a := Nat.one_le_pow a 3 (by decide)
    have hc : 8 ≤ 3 ^ a * 8 ^ b := by nlinarith
    right; right
    simpa [Nat.mul_left_comm] using Nat.mul_le_mul_left s (eight_mul_le_pow hc ht)

theorem small_orbit_parameters {s t a b : ℕ}
    (hs : 0 < s) (ht : 0 < t) (hab : 0 < a + b)
    (hd : s * (3 ^ a * 8 ^ b) ^ t ≤ 2 * (2 * (s * t) + 1)) :
    a = 1 ∧ b = 0 ∧ (t = 1 ∨ (t = 2 ∧ s ≤ 2)) := by
  rcases orbit_degree_gap (s := s) ht hab with ⟨ha, hb, ht1⟩ | ⟨ha, hb, ht2⟩ | hgap
  · exact ⟨ha, hb, Or.inl ht1⟩
  · refine ⟨ha, hb, Or.inr ⟨ht2, ?_⟩⟩
    subst a b t
    norm_num at hd
    omega
  · have hst : 0 < s * t := Nat.mul_pos hs ht
    omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
