module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.Contracts

/-!
# Prime field degree from maximality

A composite extension degree has a proper nontrivial divisor. Multiplying
that divisor by the smaller odd degree gives an intermediate odd degree,
hence an intermediate parameter. Strict subfield inclusions then contradict
maximality. This proves the prime-power field relation used in Malle's
subfield case without assuming it as part of a group identification.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open ReeF4.Subfield

/-- The subfield lattice, rather than a classification assumption, forces
a maximal proper subfield group to have prime extension degree. -/
theorem prime_degree_of_isCoatom_fixedSubfield
    (hstrict : StrictSubfieldInclusions) {m k : ℕ}
    (hlt : k < m) (hdiv : (2 * k + 1) ∣ (2 * m + 1))
    (hmax : IsCoatom (fixedSubfield m k)) :
    ∃ a, Nat.Prime a ∧ 2 ^ (2 * m + 1) = (2 ^ (2 * k + 1)) ^ a := by
  obtain ⟨a, ha⟩ := hdiv
  have ha2 : 2 ≤ a := by
    by_contra h
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp only [mul_zero, mul_one] at ha <;> omega
  refine ⟨a, ?_, ?_⟩
  · by_contra hprime
    obtain ⟨b, hba, hb2, hblt⟩ := (Nat.not_prime_iff_exists_dvd_lt ha2).mp hprime
    have hmid : (2 * k + 1) * b ∣ (2 * m + 1) := by
      rw [ha]
      exact Nat.mul_dvd_mul_left _ hba
    obtain ⟨c, hc⟩ := hmid
    have hodd : Odd (((2 * k + 1) * b) * c) := by
      rw [← hc]
      exact ⟨m, by omega⟩
    obtain ⟨l, hl⟩ := (Nat.Odd.of_mul_left hodd).exists_bit1
    have hkl : k < l := by nlinarith
    have hlm : l < m := by nlinarith
    have hdkl : (2 * k + 1) ∣ (2 * l + 1) := by
      rw [← hl]
      exact dvd_mul_right _ _
    have hdlm : (2 * l + 1) ∣ (2 * m + 1) := ⟨c, by rw [← hl, ← hc]⟩
    have hless := hstrict m k l hkl (Nat.le_of_lt hlm) hdkl hdlm
    have hproper := hstrict m l m hlm le_rfl hdlm dvd_rfl
    rw [fixedSubfield_self] at hproper
    exact hproper.ne (hmax.lt_iff.mp hless)
  · rw [← pow_mul, ← ha]

end ReeF4.MaximalSubgroups.SimpleNormal
