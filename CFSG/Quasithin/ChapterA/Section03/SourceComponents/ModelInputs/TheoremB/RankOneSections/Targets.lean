module

public import Theory.GroupTheory.SylowOuterFrattiniSections
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic.Order
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import CFSG.Quasithin.ClassicalModels

/-!
# The two rank-one targets do not occur as sections of GL₈(2)

The exact orders of PSU₃(2ˢ), s ≥ 2, and Sz(2²ᵐ⁺¹), m ≥ 1, do not divide
|GL₈(2)|. Monotonicity reduces this to s ≤ 7 and m ≤ 5, where the literal
order formulas decide the divisibility. This is the small Sylow-Frattini
obstruction used for the B-model outer sections in Aschbacher--Smith
4.4.10--11, printed p.621. All model markings are actual equivalences.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections

/-- The precise simple-quotient targets in the normalized odd-local argument. -/
def IsTarget (S : Type*) [Group S] : Prop :=
  (∃ s : ℕ, 2 ≤ s ∧ ClassicalGroup.IsPSU S 3 (2 ^ s)) ∨
    ∃ m : ℕ, 1 ≤ m ∧ Nonempty (S ≃* SuzukiMatrixGroup m)

theorem unitary_order_not_dvd_GL_eight {S : Type*} [Group S]
    {s : ℕ} (hs : 2 ≤ s) (hS : ClassicalGroup.IsPSU S 3 (2 ^ s)) :
    ¬ Nat.card S ∣ 5348063769211699200 := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hS
  rw [Nat.card_congr e.toEquiv,
    HermitianForm.UniversalCover.OddKernelBound.OddCrossCharacteristic.card_projective
      J hcard hconj]
  intro hd
  have hs8 : s < 8 := by
    by_contra! h
    have hq : 256 ≤ 2 ^ s := Nat.pow_le_pow_right (n := 2) (by decide) h
    have hnum := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 3) 1)
        (Nat.pow_le_pow_left hq 3))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have hden : Nat.gcd 3 (2 ^ s + 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
    have hb := (Nat.div_le_div_right hnum (c := 3)).trans
      (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
    have hb' : 5348063769211699200 <
        ((2 ^ s) ^ 3 + 1) * (2 ^ s) ^ 3 * ((2 ^ s) ^ 2 - 1) /
          Nat.gcd 3 (2 ^ s + 1) := lt_of_lt_of_le (by norm_num) hb
    exact (not_lt_of_ge (Nat.le_of_dvd (by norm_num) hd)) hb'
  interval_cases s <;> norm_num at hd

theorem suzuki_order_not_dvd_GL_eight {S : Type*} [Group S]
    {m : ℕ} (hm : 1 ≤ m) (e : S ≃* SuzukiMatrixGroup m) :
    ¬ Nat.card S ∣ 5348063769211699200 := by
  rw [Nat.card_congr e.toEquiv, suzukiMatrixGroup_card m (by omega)]
  intro hd
  have hm6 : m < 6 := by
    by_contra! h
    have hq : 8192 ≤ 2 ^ (2 * m + 1) :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 13 ≤ 2 * m + 1)
    have hb := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.pow_le_pow_left hq 2) 1)
        (Nat.pow_le_pow_left hq 2)) (Nat.sub_le_sub_right hq 1)
    have hb' : 5348063769211699200 <
        ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 *
          (2 ^ (2 * m + 1) - 1) := lt_of_lt_of_le (by norm_num) hb
    exact (not_lt_of_ge (Nat.le_of_dvd (by norm_num) hd)) hb'
  interval_cases m <;> norm_num at hd

theorem IsTarget.order_not_dvd_GL_eight {S : Type*} [Group S] (hS : IsTarget S) :
    ¬ Nat.card S ∣ 5348063769211699200 := by
  rcases hS with ⟨s,hs,hu⟩ | ⟨m,hm,⟨e⟩⟩
  · exact unitary_order_not_dvd_GL_eight hs hu
  · exact suzuki_order_not_dvd_GL_eight hm e

end CFSG.Quasithin.ChapterA.Section03.SourceComponents.TheoremBOuter.RankOneSections
