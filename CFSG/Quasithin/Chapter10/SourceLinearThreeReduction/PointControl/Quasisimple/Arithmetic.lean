module
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General

/-!
# A scalar prime avoiding binary field automorphisms

For n > 1 there is an odd prime dividing 2^n-1 and prime to n.
A primitive prime divisor works except at n=6, where seven works.
This chooses only the prime needed by the symplectic torus argument
in Aschbacher--Smith 10.2.9, printed pp.750--751.
-/

public section
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple

theorem exists_scalar_prime {n : ℕ} (hn : 1 < n) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ n - 1 ∧ Nat.Coprime p n := by
  by_cases h6 : n = 6
  · subst n
    exact ⟨7,by decide,by decide,by decide,by decide⟩
  obtain ⟨p,hp,hord⟩ := Theory.NumberTheory.exists_prime_orderOf_two hn h6
  let : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    rw [hz,orderOf_zero] at hord
    omega
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h2 (ZMod.natCast_self 2)
  have hnp : n < p := by
    have hd := ZMod.orderOf_dvd_card_sub_one h2
    rw [hord] at hd
    have hle := Nat.le_of_dvd (Nat.sub_pos_of_lt hp.one_lt) hd
    omega
  have he : (2 : ZMod p) ^ n = 1 := hord ▸ pow_orderOf_eq_one (2 : ZMod p)
  have hd : p ∣ 2 ^ n - 1 := by
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
    rw [Nat.cast_sub hpow,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,he,sub_self]
  exact ⟨p,hp,hp2,hd,hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (by omega) hnp)⟩

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
