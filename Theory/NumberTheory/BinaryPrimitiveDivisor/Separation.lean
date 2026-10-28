module
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General

/-!
# Separating primes for unequal binary field orders

For 0 < a < b there is a prime dividing 2^b-1 but not 2^a-1.
Use the primitive-divisor theorem away from exponent six. At six, seven
works for a=1,2,4,5 and three works for a=3. This is a separating prime,
not a nonexistent primitive divisor of 2^6-1. The literal rank-one Cartan
construction in HexagonStructure.MiddleIsolation consumes this result.

Source: Fong--Seitz I (4G), (6E), printed pp.23--24,44, specialized to p=2.
-/

public section
namespace Theory.NumberTheory

/-- Binary prime separation includes the exceptional Zsigmondy exponent six.
At six use seven, or three when the smaller exponent is three. -/
theorem exists_binary_separating_prime {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2^b-1 ∧ ¬ r ∣ 2^a-1 := by
  by_cases hb : b = 6
  · subst b
    interval_cases a <;> norm_num at *
    · exact ⟨7,by decide,by norm_num,by norm_num⟩
    · exact ⟨7,by decide,by norm_num,by norm_num⟩
    · exact ⟨3,by decide,by norm_num,by norm_num⟩
    · exact ⟨7,by decide,by norm_num,by norm_num⟩
    · exact ⟨7,by decide,by norm_num,by norm_num⟩
  · obtain ⟨r,hr,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two (by omega) hb
    have hpow (n : ℕ) : r ∣ 2^n-1 ↔ (2 : ZMod r)^n = 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))),
        Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, sub_eq_zero]
    refine ⟨r,hr,(hpow b).mpr ?_,?_⟩
    · rw [← ho]
      exact pow_orderOf_eq_one _
    · intro hd
      have hh := orderOf_dvd_of_pow_eq_one ((hpow a).mp hd)
      rw [ho] at hh
      exact (not_le_of_gt hab) (Nat.le_of_dvd ha hh)

end Theory.NumberTheory
