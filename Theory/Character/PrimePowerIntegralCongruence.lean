module

public import Theory.Character.ClassFunction
public import Theory.Character.PrimePowerTrace

/-!
# Integral character values on prime-power elements

An integer character value at a prime-power element is congruent to the degree
modulo the prime. The identity operator case is immediate; otherwise Schur's
prime-power trace spacing theorem gives the divisibility. No irreducibility or
rational realization of the representation is required.

Source: Schur's prime-power trace argument; see `PrimePowerTrace`.
-/

noncomputable section

/-- Integral values at prime-power elements are congruent to the degree. -/
public theorem IsCharacter.prime_dvd_degree_sub_integer_value
    {G : Type*} [Group G] {χ : ClassFunction G} (hχ : IsCharacter χ)
    (g : G) {p k : ℕ} (hp : p.Prime) (hg : g ^ (p ^ k) = 1)
    (n a : ℤ) (hn : χ 1 = (n : ℂ)) (ha : χ g = (a : ℂ)) :
    (p : ℤ) ∣ n - a := by
  obtain ⟨m, ρ, rfl⟩ := hχ
  have hmn : (m : ℤ) = n := by
    have hh : (m : ℂ) = (n : ℂ) := by simpa using hn
    exact_mod_cast hh
  by_cases he : ρ g = 1
  · have hma : (m : ℤ) = a := by
      have hh : (m : ℂ) = (a : ℂ) := by
        simpa [Representation.character, he] using ha
      exact_mod_cast hh
    rw [← hmn, hma, sub_self]
    exact dvd_zero _
  · have hpow : (ρ g) ^ (p ^ k) = 1 := by rw [← map_pow, hg, map_one]
    obtain ⟨j, _, hj⟩ := prime_power_trace_spacing_of_rational (ρ g) hp hpow he
      ⟨(a : ℚ), by simpa [Representation.character] using ha⟩
    have hh : a = (m : ℤ) - p * (j + 1) := by
      have hc : (a : ℂ) = (m : ℂ) - p * (j + 1) := by
        change ρ.character g = _ at hj
        simpa [ha] using hj
      exact_mod_cast hc
    exact ⟨j + 1, by rw [← hmn, hh]; ring⟩
