module
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-!
# The small-degree inequality for Suzuki tensor supports

If a nonempty tensor support has size `r` and Frobenius orbit size `d`,
then its binary dimension is `4^r*d` and the field exponent `n` divides `r*d`.
For odd `n`, a dimension below `10*n` forces `r=1`. For `r≥3` use
`10*r ≤ 4^r`; for `r=2`, oddness forces `n∣d`.

This is the numerical exclusion in Guralnick–Malle, *Classification of
2F-modules, II*, Lemma 8.3. Construction of the tensor support and its
field of definition is a separate representation-theoretic obligation.
-/

public section
namespace Representation.SuzukiSmallDegree

private theorem ten_mul_le_four_pow {r : ℕ} (hr : 3 ≤ r) : 10 * r ≤ 4 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [pow_succ]
    nlinarith

/-- Every support of at least two factors violates the Suzuki degree window.
The divisibility is the orbit-counting consequence of field descent. -/
theorem tensor_degree_ge {n r d : ℕ} (hn : Odd n) (hr : 2 ≤ r)
    (hd : 0 < d) (hperiod : n ∣ r * d) : 10 * n ≤ 4 ^ r * d := by
  by_cases htwo : r = 2
  · subst r
    have hnd : n ∣ d := hn.coprime_two_right.dvd_of_dvd_mul_left hperiod
    have hle : n ≤ d := Nat.le_of_dvd hd hnd
    norm_num
    omega
  · have hnr : n ≤ r * d := Nat.le_of_dvd (Nat.mul_pos (by omega) hd) hperiod
    calc
      10 * n ≤ 10 * (r * d) := Nat.mul_le_mul_left 10 hnr
      _ = (10 * r) * d := by ring
      _ ≤ 4 ^ r * d := Nat.mul_le_mul_right d (ten_mul_le_four_pow (by omega))

/-- The source small-degree bound leaves exactly one natural tensor factor. -/
theorem tensor_support_eq_one {m r d D : ℕ} (hr : 0 < r) (hd : 0 < d)
    (hperiod : 2 * m + 1 ∣ r * d) (hdegree : D = 4 ^ r * d)
    (hsmall : D < 10 * (2 * m + 1)) : r = 1 := by
  by_contra hne
  have hlarge := tensor_degree_ge (n := 2 * m + 1) ⟨m, rfl⟩ (by omega : 2 ≤ r) hd hperiod
  omega

end Representation.SuzukiSmallDegree
