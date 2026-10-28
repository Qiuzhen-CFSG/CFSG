module
public import Theory.NumberTheory.BinarySignedTorus
/-!
# A binary minus torus supported only at three

Every divisor of 2ⁿ − 1 is odd for n > 0. If n > 1 and all prime divisors
are three, BinarySignedTorus excludes n > 3 and the explicit factor seven
excludes n = 3. Thus n = 2, as in Aschbacher–Smith 2.5.7, printed p.556.
-/
public section
namespace Nat.BinarySignedTorus

theorem odd_of_dvd_sub {n p : ℕ} (hn : 0<n) (hd : p ∣ 2^n-1) : Odd p := by
  apply Odd.of_dvd_nat (n:=2^n-1) _ hd
  rw [Nat.odd_iff]
  have h2 : 2 ∣ 2^n := dvd_pow_self 2 (by omega)
  have hmod:=Nat.mod_eq_zero_of_dvd h2
  have hpos : 0 < (2:ℕ)^n := pow_pos (by decide) _
  omega

theorem exponent_eq_two_of_prime_dvd_eq_three {n : ℕ} (hn : 1<n)
    (h : ∀ p : ℕ, p.Prime → p ∣ 2^n-1 → p=3) : n=2 := by
  have hle : n≤3 := by
    by_contra hn3
    obtain ⟨p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega : 3<n)
    have := h p hp hd
    omega
  have hn3 : n≠3 := by
    intro he
    have hp:=h 7 (by decide) (by rw [he];decide)
    omega
  omega
end Nat.BinarySignedTorus
