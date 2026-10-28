module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Remaining

/-!
# The strict degree gap for the remaining tensor words

Removing the single adjoint from the non-small repeated words improves the
binary dimension lower bound from eight to nine times the defining exponent.
For a tensor square of size three, non-smallness also forces Schur degree at
least two. These facts close the numerical ends of the common-fixed-space
argument; they assume no actor estimate.

Source: the tensor dimensions in Guralnick–Malle, Classification of 2F-modules
II, Proposition 4.8, manuscript pp.26–28, applied to SL₃ in K.3.2.
-/

public section
open Representation Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors

private theorem nine_mul_le_pow {c t : ℕ} (hc : 9 ≤ c) (ht : 0 < t) :
    9 * t ≤ c ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hc
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem nine_mul_le_three_pow {t : ℕ} (ht : 3 ≤ t) : 9 * t ≤ 3 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem nine_mul_le_eight_pow {t : ℕ} (ht : 2 ≤ t) : 9 * t ≤ 8 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem thirty_two_mul_le_pow {c t : ℕ} (hc : 32 ≤ c) (ht : 0 < t) :
    32 * t ≤ c ^ t := by
  induction t, ht using Nat.le_induction with
  | base => simpa using hc
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem thirty_two_mul_le_eight_pow {t : ℕ} (ht : 2 ≤ t) :
    32 * t ≤ 8 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih => rw [pow_succ]; nlinarith

private theorem remaining_degree_gap {a b t : ℕ} (ht : 0 < t) (hp : 0 < a + b)
    (hn : ¬ (a = 1 ∧ b = 0 ∧ (t = 1 ∨ t = 2)))
    (hj : ¬ (a = 0 ∧ b = 1 ∧ t = 1)) :
    9 * t ≤ (3 ^ a * 8 ^ b) ^ t := by
  by_cases hb : b = 0
  · subst b
    by_cases ha : a = 1
    · subst a
      simpa using nine_mul_le_three_pow (by simp only [true_and] at hn; omega)
    · have ha2 : 2 ≤ a := by omega
      have hpow : 9 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) ha2
      simpa using nine_mul_le_pow hpow ht
  · have hb1 : 1 ≤ b := by omega
    have h8 : 8 ≤ 8 ^ b := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb1
    by_cases ha : a = 0
    · subst a
      by_cases hb' : b = 1
      · subst b
        simpa using nine_mul_le_eight_pow (by simp only [true_and] at hj; omega)
      · have hb2 : 2 ≤ b := by omega
        have h64 : 64 ≤ 8 ^ b := by
          simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb2
        simpa using nine_mul_le_pow (by omega : 9 ≤ 8 ^ b) ht
    · have h3 : 3 ≤ 3 ^ a := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 1 ≤ a)
      exact nine_mul_le_pow (by nlinarith) ht

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- The remaining words have binary dimension at least nine times the field exponent. -/
theorem nine_mul_degree_le_finrank (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hj : ¬ SingleAdjoint B σ M) :
    9 * B.degree ≤ Module.finrank (ZMod 2) V := by
  have h := remaining_degree_gap M.repetitions_pos hp hn hj
  rw [M.field_degree, M.finrank_eq]
  simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left (schurDegree σ) h

/-- Pure-adjoint words other than the single adjoint have a much larger gap. -/
theorem thirty_two_mul_degree_le_finrank (M : RepeatedModel B σ)
    (ha : naturalCount M.block = 0) (hb : 0 < adjointCount M.block)
    (hj : ¬ SingleAdjoint B σ M) :
    32 * B.degree ≤ Module.finrank (ZMod 2) V := by
  have h : 32 * M.repetitions ≤ (8 ^ adjointCount M.block) ^ M.repetitions := by
    by_cases hb1 : adjointCount M.block = 1
    · have ht2 : 2 ≤ M.repetitions := by
        have ht := M.repetitions_pos
        have hne : M.repetitions ≠ 1 := fun he => hj ⟨ha, hb1, he⟩
        omega
      simpa [hb1] using thirty_two_mul_le_eight_pow ht2
    · have hb2 : 2 ≤ adjointCount M.block := by omega
      have hp : 64 ≤ 8 ^ adjointCount M.block := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 8) hb2
      exact thirty_two_mul_le_pow (by omega) M.repetitions_pos
  rw [M.field_degree, M.finrank_eq, ha, pow_zero, one_mul]
  simpa only [Nat.mul_left_comm] using Nat.mul_le_mul_left (schurDegree σ) h

private theorem counts_le_length (w : List Factor) :
    naturalCount w + adjointCount w ≤ w.length := by
  induction w with
  | nil => simp [naturalCount, adjointCount]
  | cons a w ih =>
    cases a <;> simp [naturalCount, adjointCount] at ih ⊢ <;> omega

/-- A non-small tensor square of size three cannot have binary Schur degree one. -/
theorem two_le_schurDegree_of_square_three (M : RepeatedModel B σ)
    (hp : 0 < naturalCount M.block + adjointCount M.block) (hn : ¬ M.Small)
    (hj : ¬ SingleAdjoint B σ M)
    (hd : Module.finrank (ZMod 2) V = schurDegree σ * 9) :
    2 ≤ schurDegree σ := by
  have hs := schurDegree_pos σ
  have hgap := nine_mul_degree_le_finrank B σ M hp hn hj
  have ht := M.repetitions_pos
  rw [hd, M.field_degree] at hgap
  have ht1 : M.repetitions = 1 := by nlinarith
  by_contra h
  have hs1 : schurDegree σ = 1 := by omega
  have hc := counts_le_length M.block
  rw [M.block_length, hs1] at hc
  have he := M.finrank_eq
  rw [hd, hs1, ht1, one_mul, one_mul, pow_one] at he
  rcases (by omega : (naturalCount M.block = 1 ∧ adjointCount M.block = 0) ∨
    (naturalCount M.block = 0 ∧ adjointCount M.block = 1)) with h | h
  · simp [h.1, h.2] at he
  · simp [h.1, h.2] at he

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors
