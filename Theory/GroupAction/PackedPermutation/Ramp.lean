module
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Linarith

/-!
# A closed packed identity table

The arithmetic-geometric sum gives a closed natural-number expression for the
base-`2^w` numeral with digits `0,1,...,n-1`. The digit proof uses `Nat.ofDigits`;
the closed formula lets kernel certificates construct large identity tables
without reducing a recursion of length `n`.

The switching-network consumer compares the resulting packed tables with the
literal ATLAS generator data for the Fi24 involution-centralizer section.
-/
namespace Theory.GroupAction.PackedPermutation

private def rampBase (q n : Nat) : Nat :=
  (n * q ^ (n + 1) + q - (n * q ^ n + q ^ (n + 1))) / (q - 1) ^ 2

private lemma ramp_digits_succ (q n : Nat) :
    Nat.ofDigits q (List.range (n+1)) =
      Nat.ofDigits q (List.range n) + q ^ n * n := by
  rw [List.range_succ, Nat.ofDigits_append]
  simp

private lemma ramp_polynomial (b n : Nat) :
    Nat.ofDigits (b+1) (List.range n) * b^2 + n*(b+1)^n + (b+1)^(n+1) =
      n*(b+1)^(n+1)+(b+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ramp_digits_succ]
    simp only [pow_succ] at ih ⊢
    nlinarith only [ih]

private lemma ramp_eq_digits {q : Nat} (hq : 1 < q) (n : Nat) :
    rampBase q n = Nat.ofDigits q (List.range n) := by
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hb : b ≠ 0 := by omega
  have H := ramp_polynomial b n
  unfold rampBase
  simp only [Nat.succ_sub_one]
  have he : n*(b+1)^(n+1)+(b+1) - (n*(b+1)^n+(b+1)^(n+1)) =
      Nat.ofDigits (b+1) (List.range n)*b^2 := by omega
  rw [he, Nat.mul_div_left _ (pow_pos (by omega) _)]

private lemma ramp_get {q n i : Nat} (hq : 1 < q) (hn : n ≤ q) (hi : i < n) :
    (rampBase q n / q ^ i) % q = i := by
  rw [ramp_eq_digits hq,
    Nat.ofDigits_div_pow_eq_ofDigits_drop i (by omega) _ (by
      intro x hx
      exact lt_of_lt_of_le (List.mem_range.mp hx) hn), Nat.ofDigits_mod_eq_head!]
  rw [List.head!_eq_head?_getD, List.head?_drop]
  simp only [List.getElem?_range hi, Option.getD_some]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hi hn)

private lemma ramp_shift_get {w n i : Nat} (hw : 0 < w) (hn : n ≤ 2^w) (hi : i < n) :
    ((rampBase (2^w) n) >>> (w*i)) % 2^w = i := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact ramp_get (one_lt_pow₀ (by decide) (by omega)) hn hi

/-- Closed packed identity table with field width `w` and `n` entries. -/
@[expose] public def ramp (w n : Nat) : Nat :=
  let q := 2^w
  (n*q^(n+1)+q-(n*q^n+q^(n+1))) / (q-1)^2

public theorem ramp_eq_ofDigits {w : Nat} (hw : 0 < w) (n : Nat) :
    ramp w n = Nat.ofDigits (2^w) (List.range n) :=
  ramp_eq_digits (one_lt_pow₀ (by decide) (by omega)) n

/-- Every original wire number is recovered from its packed field. -/
public theorem get_ramp {w n i : Nat} (hw : 0 < w)
    (hn : n ≤ 2^w) (hi : i < n) :
    ((ramp w n) >>> (w*i)) % 2^w = i :=
  ramp_shift_get hw hn hi

public theorem ramp_lt {w n : Nat} (hw : 0 < w) (hn : n ≤ 2^w) :
    ramp w n < 2^(w*n) := by
  rw [ramp_eq_ofDigits hw]
  simpa only [List.length_range, ← pow_mul] using
    Nat.ofDigits_lt_base_pow_length (one_lt_pow₀ (by decide) (by omega))
      (fun x hx => lt_of_lt_of_le (List.mem_range.mp hx) hn)

end Theory.GroupAction.PackedPermutation
