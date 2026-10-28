module

public import Theory.SpecificGroups.Lyons.Atlas111WordRelations.Arithmetic

/-!
# Packed column arithmetic for the Lyons plane orbit

The orbit producer packs columns in base eight. We widen their digits into
radix 3125, reusing the checked word-certificate encoding. A linear combination
then computes 111 coordinates simultaneously. Generator coefficients are at
most four, so even arbitrary base-eight digits give coefficients at most
`111 * 4 * 7 = 3108 < 3125`. No validity assumption on producer data is needed.

Source format: `../Atlas111PlaneOrbitSource/README.md` and `GenerateOrbit.py`.
-/

@[expose] public section
namespace Lyons.OrderCertificate.PlaneOrbitArithmetic
open Atlas111WordCertificate

/-- A least-significant-first base-eight digit from the producer. -/
def digit8 (a i : ℕ) : ℕ := a / 8 ^ i % 8

theorem digit8_succ (a i : ℕ) : digit8 a (i+1) = digit8 (a/8) i := by
  simp only [digit8, pow_succ', Nat.div_div_eq_div_mul]

theorem digit8_le (a i : ℕ) : digit8 a i ≤ 7 := by
  have := Nat.mod_lt (a / 8^i) (by decide : 0 < 8)
  unfold digit8
  omega

/-- Widen a producer column without changing its digits. -/
def widen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, a => a % 8 + radix * widen n (a/8)

theorem widen_eq_encode (n a : ℕ) : widen n a = encode n (digit8 a) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [widen, encode, ih, digit8_succ]
    unfold digit8
    simp only [pow_zero, Nat.div_one]

theorem digit_widen (n a i : ℕ) (hi : i < n) :
    digit (widen n a) i = digit8 a i := by
  rw [widen_eq_encode]
  exact digit_encode _ _ (fun j _ => lt_of_le_of_lt (digit8_le a j) (by decide)) i hi

/-- Packed linear combination, with coefficients read directly from base eight. -/
def combine (columns : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => combine columns a n + digit8 a n * columns n

theorem combine_eq_sum (columns : ℕ → ℕ) (a n : ℕ) :
    combine columns a n = ∑ k : Fin n, digit8 a k * columns k := by
  induction n with
  | zero => simp [combine]
  | succ n ih => simp only [combine, ih, Fin.sum_univ_castSucc,
      Fin.val_castSucc, Fin.val_last]

/-- Carry-free extraction for rectangular products; the finite-sum proof is
reused from the word-certificate arithmetic. -/
theorem combine_digit (m n d : ℕ) (columns : ℕ → ℕ) (f : ℕ → ℕ → ℕ) (a : ℕ)
    (hc : ∀ k < n, columns k = encode m (f k))
    (hf : ∀ k < n, ∀ i < m, f k i ≤ d) (hd : n * (7*d) < radix)
    (i : ℕ) (hi : i < m) :
    digit (combine columns a n) i = ∑ k : Fin n, digit8 a k * f k i := by
  have he : combine columns a n =
      encode m (fun j => ∑ k : Fin n, digit8 a k * f k j) := by
    rw [encode_sum]
    simp only [encode_mul, combine_eq_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hc k k.isLt]
  rw [he]
  apply digit_encode _ _ _ i hi
  intro j hj
  have hb : (∑ k : Fin n, digit8 a k * f k j) ≤ ∑ _k : Fin n, 7*d := by
    apply Finset.sum_le_sum
    intro k _
    exact Nat.mul_le_mul (digit8_le a k) (hf k k.isLt j hj)
  have hs : (∑ _k : Fin n, 7*d) = n*(7*d) := by simp
  rw [hs] at hb
  exact lt_of_le_of_lt hb hd

/-- Compare unreduced packed products, reducing each lane modulo five. -/
def residuesEq : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | n+1, a, b => (a % radix % 5 == b % radix % 5) &&
      residuesEq n (a/radix) (b/radix)

theorem residuesEq_sound (n a b : ℕ) (h : residuesEq n a b = true)
    (i : ℕ) (hi : i < n) : (digit a i : ZMod 5) = (digit b i : ZMod 5) := by
  induction n generalizing a b i with
  | zero => omega
  | succ n ih =>
    simp only [residuesEq, Bool.and_eq_true, beq_iff_eq] at h
    cases i with
    | zero =>
      simp only [digit, pow_zero, Nat.div_one]
      rw [← ZMod.natCast_mod (a % radix), ← ZMod.natCast_mod (b % radix), h.1]
    | succ i =>
      simpa only [digit_succ] using ih _ _ h.2 i (by omega)
end Lyons.OrderCertificate.PlaneOrbitArithmetic
