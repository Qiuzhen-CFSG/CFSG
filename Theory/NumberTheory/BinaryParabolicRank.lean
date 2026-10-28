module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# The intermediate degree in a binary parabolic

A divisor k of 4n strictly between n and 2n satisfies 3k = 4n.
If an actor rank a is a multiple of k, lies below 4n, and k+a is at least
5n, then a = 4n. Divisibility of k+a by n now contradicts n < k < 2n.
An odd k is excluded directly by coprimality with 4.

These are the degree constraints used in the Hermitian tensor argument in
Aschbacher–Smith 8.2.3, printed pp.715–716. They do not infer a split-torus
order from preservation of a maximal parabolic.
-/

public section
namespace Nat.BinaryParabolicRank

/-- The only divisor of `4n` strictly between `n` and `2n` is `4n/3`. -/
theorem oversized_divisor_four {n k : ℕ} (hnk : n < k) (hkn : k < 2 * n)
    (hk : k ∣ 4 * n) : 3 * k = 4 * n := by
  obtain ⟨d, hd⟩ := hk
  have hkpos : 0 < k := by omega
  have hdlo : 3 ≤ d := by
    by_contra h
    have hm := Nat.mul_le_mul_left k (show d ≤ 2 by omega)
    omega
  have hdhi : d ≤ 3 := by
    by_contra h
    have hm := Nat.mul_le_mul_left k (show 4 ≤ d by omega)
    omega
  have : d = 3 := by omega
  subst d
  omega

/-- The fixed-space degree and actor degrees exclude the nonsplit intermediate case. -/
theorem false_of_intermediate_parameters {n k a : ℕ}
    (hnk : n < k) (hkn : k < 2 * n) (hk : k ∣ 4 * n)
    (ha : a ≤ 4 * n) (hcodim : 5 * n ≤ k + a)
    (hdegree : k ∣ a ∨ Odd k) (hfixed : n ∣ k + a) : False := by
  have hthree := oversized_divisor_four hnk hkn hk
  have hn : 0 < n := by omega
  have hkpos : 0 < k := by omega
  rcases hdegree with hdegree | hodd
  · obtain ⟨r, hr⟩ := hdegree
    have hrlo : 3 ≤ r := by
      by_contra h
      have hm := Nat.mul_le_mul_left k (show r ≤ 2 by omega)
      omega
    have hrhi : r ≤ 3 := by
      by_contra h
      have hm := Nat.mul_le_mul_left k (show 4 ≤ r by omega)
      omega
    have hr3 : r = 3 := by omega
    rw [hr3] at hr
    have he : a = 4 * n := by omega
    rw [he] at hfixed
    have hnkdiv : n ∣ k := (Nat.dvd_add_iff_left (dvd_mul_left n 4)).mpr hfixed
    obtain ⟨s, hs⟩ := hnkdiv
    have hslo : 2 ≤ s := by
      by_contra h
      have hm := Nat.mul_le_mul_left n (show s ≤ 1 by omega)
      omega
    have hm := Nat.mul_le_mul_left n hslo
    omega
  · have hcop : Nat.Coprime k 4 := by
      have hc : Nat.Coprime k 2 := (Nat.coprime_two_right).mpr hodd
      simpa using hc.pow_right 2
    have hknDiv : k ∣ n := hcop.dvd_of_dvd_mul_left hk
    have : k ≤ n := Nat.le_of_dvd hn hknDiv
    omega

end Nat.BinaryParabolicRank
