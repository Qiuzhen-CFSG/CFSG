module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.OrbitBounds

/-!
# The next gap in the G₂ Frobenius degree formula

Products of the restricted degrees 1, 6, 14 and 64 are either 1, 6, 14 or
at least 36. A nontrivial Frobenius block repeated at least twice has binary
degree at least eighteen times the defining-field exponent. Below that bound
the Schur field has full degree and the block has dimension six or fourteen.

These arithmetic facts consume the genuine tensor parameters in
`AdjointRecognition.lean`; they assume no representation classification.
Source: GLS3 2.8.6–2.8.10(g), used in GM04 Lemma 8.5, pp.55–56.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition

/-- The four restricted factors have no product dimension strictly between fourteen and thirty-six. -/
theorem basic_product_gap (l : List ℕ)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64) :
    l.prod = 1 ∨ l.prod = 6 ∨ l.prod = 14 ∨ 36 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have hb := ih (fun b hb => hl b (by simp [hb]))
    simp only [List.prod_cons]
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with hb | hb | hb | hb
    all_goals omega

private theorem eighteen_mul_le_six_pow {t : ℕ} (ht : 2 ≤ t) :
    18 * t ≤ 6 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

/-- Below the repeated-block bound, only full-period natural and adjoint blocks remain. -/
theorem parameters_below_eighteen {n d s t : ℕ} (l : List ℕ)
    (hs : 0 < s) (ht : 0 < t)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64)
    (hne : l.prod ≠ 1) (hn : n = s * t) (hd : d = s * l.prod ^ t)
    (hb : d < 18 * n) : s = n ∧ t = 1 ∧ (l.prod = 6 ∨ l.prod = 14) := by
  have hp := basic_product_gap l hl
  have hge : 6 ≤ l.prod := by omega
  have ht1 : t = 1 := by
    by_contra h
    have hh := (eighteen_mul_le_six_pow (by omega : 2 ≤ t)).trans
      (Nat.pow_le_pow_left hge t)
    have hh' : 18 * n ≤ d := calc
      18 * n = s * (18 * t) := by rw [hn]; ring
      _ ≤ s * l.prod ^ t := Nat.mul_le_mul_left s hh
      _ = d := hd.symm
    exact (not_lt_of_ge hh') hb
  have hsn : s = n := by simpa [ht1] using hn.symm
  refine ⟨hsn, ht1, ?_⟩
  rw [ht1, pow_one] at hd
  rw [← hsn, hd, Nat.mul_comm 18 s] at hb
  have hlt : l.prod < 18 := (Nat.mul_lt_mul_left hs).mp hb
  rcases hp with hp | hp | hp | hp
  · exact (hne hp).elim
  · exact Or.inl hp
  · exact Or.inr hp
  · omega

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
