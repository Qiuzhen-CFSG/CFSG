module
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic
/-!
# Closed periodic field masks

A repeated word is represented by a geometric quotient, rather than an
n-element list. The proof compares it symbolically with base-two-power
digits; extraction gives the exact repeated word below the field bound and
zero above it. This supplies the boundary-aware masks in the Fi24 packed
switching certificates without expanding one declaration per field.
-/
@[expose] public section
namespace Theory.GroupAction.PackedPermutation

def repeatField (w n c : ℕ) : ℕ := c*((2^(w*n)-1)/(2^w-1))

private theorem replicate_one (B n : ℕ) (hB : 1<B) :
    1+(B-1)*Nat.ofDigits B (List.replicate n 1) = B^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, Nat.ofDigits_cons, pow_succ]
    have hsub : B-1+1=B := by omega
    nlinarith

private theorem replicate_mul (B n c : ℕ) :
    Nat.ofDigits B (List.replicate n c) = c*Nat.ofDigits B (List.replicate n 1) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, Nat.ofDigits_cons, ih]; ring

theorem repeatField_eq_ofDigits (w n c : ℕ) (hw : 0<w) :
    repeatField w n c = Nat.ofDigits (2^w) (List.replicate n c) := by
  have hB : 1<2^w := Nat.one_lt_pow hw.ne' (by decide)
  have h := replicate_one (2^w) n hB
  have he : (2^w)^n-1 = (2^w-1)*Nat.ofDigits (2^w) (List.replicate n 1) := by omega
  rw [repeatField, Nat.pow_mul, he]
  rw [Nat.mul_div_cancel_left _ (by omega : 0<2^w-1)]
  exact (replicate_mul (2^w) n c).symm

theorem repeatField_get (w n c i : ℕ) (hw : 0<w) (hc : c<2^w) :
    (repeatField w n c >>> (w*i)) % 2^w = if i<n then c else 0 := by
  rw [repeatField_eq_ofDigits w n c hw, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop]
  · rw [List.drop_replicate, Nat.ofDigits_mod_eq_head!]
    by_cases hi : i<n
    · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show n-i≠0 by omega)
      rw [hk]
      simp [hi, List.replicate_succ, hc, Nat.mod_eq_of_lt]
    · have h : n-i=0 := by omega
      simp [hi,h]
  · exact Nat.two_pow_pos w
  · intro d hd
    have := List.mem_replicate.mp hd
    simpa only [this.2] using hc
end Theory.GroupAction.PackedPermutation
