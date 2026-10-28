module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Bounded checks for the Fi23 lift tables

Balanced Boolean checks keep the reduction depth logarithmic. Their soundness
turns small kernel-checked blocks into pointwise identities on the exact finite
letter sets used by the Fi23 centralizer calculation (GLS3 Table 5.3u).
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate

def checkRange (f : Nat → Bool) : Nat → Nat → Bool
  | 0, start => f start
  | d + 1, start => checkRange f d start && checkRange f d (start + 2^d)

theorem checkRange_spec (f : Nat → Bool) (d start : Nat) :
    checkRange f d start = true ↔
      ∀ i, start ≤ i → i < start + 2^d → f i = true := by
  induction d generalizing start with
  | zero =>
    simp only [checkRange, pow_zero]
    constructor
    · intro h i hi hi'
      have : i = start := by omega
      simpa [this] using h
    · intro h
      exact h start le_rfl (by omega)
  | succ d ih =>
    rw [checkRange, Bool.and_eq_true, ih, ih, pow_succ]
    constructor
    · rintro ⟨hl, hr⟩ i hi hi'
      by_cases h : i < start + 2^d
      · exact hl i hi h
      · exact hr i (by omega) (by omega)
    · intro h
      exact ⟨fun i hi hi' => h i hi (by omega),
        fun i hi hi' => h i (by omega) (by omega)⟩

def checkAt {n : Nat} [NeZero n] (P : Fin n → Prop) [DecidablePred P]
    (i : Nat) : Bool := if i < n then decide (P (Fin.ofNat n i)) else true

theorem of_check_blocks {n d count : Nat} [NeZero n]
    (P : Fin n → Prop) [DecidablePred P] (hsize : n ≤ 2^d * count)
    (h : ∀ b : Fin count, checkRange (checkAt P) d (2^d * b.val) = true)
    (i : Fin n) : P i := by
  have hp : 0 < 2^d := Nat.two_pow_pos d
  have hb : i.val / 2^d < count := (Nat.div_lt_iff_lt_mul hp).mpr
    (by simpa only [Nat.mul_comm] using i.isLt.trans_le hsize)
  have hmod := Nat.mod_lt i.val hp
  have hdiv := Nat.mod_add_div i.val (2^d)
  have hi := (checkRange_spec _ d _).mp (h ⟨i.val / 2^d, hb⟩) i.val
    (by change 2^d * (i.val / 2^d) ≤ i.val; omega)
    (by change i.val < 2^d * (i.val / 2^d) + 2^d; omega)
  have hcast : Fin.ofNat n i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simpa only [checkAt, if_pos i.isLt, hcast, decide_eq_true_eq] using hi

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
