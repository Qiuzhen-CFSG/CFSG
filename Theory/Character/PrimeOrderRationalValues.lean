module

public import Theory.Character.ColumnBound
public import Theory.Character.FiniteOrderTrace
public import Theory.Character.Integrality
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Rational irreducible character values at prime-order elements

A rational character value is an integer because it is an algebraic integer.
At an element whose order divides a prime, that integer is congruent to the
degree modulo the prime. Column orthogonality bounds its square by the order
of the element centralizer. Together these statements often determine the
value from the degree without using modular block theory.

The congruence is the prime-order trace congruence of
`Theory.Character.FiniteOrderTrace`; the bound is second orthogonality.
Source application: Alperin--Brauer--Gorenstein, III.8 Proposition 5,
printed p.117, the rational degree-27 and degree-12 rows at elements of order 13.
-/

noncomputable section
namespace PrimeOrderRationalValues
variable {G : Type*} [Group G] [Finite G]

/-- A rational irreducible character value is an integer whose residue is its
degree modulo the prime and whose square is bounded by the centralizer order. -/
public theorem integer_value_congruence_bound {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) {p n : ℕ} (hp : p.Prime)
    (hd : χ (ConjClasses.mk 1) = (n : ℂ)) (g : G) (hg : g ^ p = 1)
    (hrat : ∃ q : ℚ, χ (ConjClasses.mk g) = (q : ℂ)) :
    ∃ z : ℤ, χ (ConjClasses.mk g) = (z : ℂ) ∧ (p : ℤ) ∣ z - n ∧
      z ^ 2 ≤ (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℤ) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨m, ρ, hρ⟩ := hχ.1
  have hi : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using hχ.2)
  have hm : m = n := by
    have hd' : ρ.character 1 = (n : ℂ) := by rw [hρ] at hd; exact hd
    have he : (m : ℂ) = (n : ℂ) := by simpa using hd'
    exact_mod_cast he
  have hint : IsIntegral ℤ (χ (ConjClasses.mk g)) := by
    rw [hρ]
    exact character_value_isIntegral ρ g
  obtain ⟨q, hq⟩ := hrat
  rw [hq] at hint
  have hqint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  have hzval : χ (ConjClasses.mk g) = (z : ℂ) := by rw [hq, ← hz]; simp
  refine ⟨z, hzval, ?_, ?_⟩
  · have ht : LinearMap.trace ℂ (Fin m → ℂ) (ρ g) = (z : ℂ) := by
      rw [hρ] at hzval
      exact hzval
    have hpow : (ρ g) ^ p = 1 := by rw [← map_pow, hg, map_one]
    simpa [hm] using prime_dvd_integer_trace_sub_finrank (ρ g) hp hpow z ht
  · have hirr : IsIrreducibleCharacter ρ.character := ⟨m, ρ, hi, rfl⟩
    have hb := hirr.normSq_le_centralizer_card g
    have he : ρ.character g = (z : ℂ) := by
      rw [hρ] at hzval
      exact hzval
    rw [he] at hb
    have hb' : (z : ℝ) ^ 2 ≤ (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
      simpa [Complex.normSq_apply, pow_two] using hb
    exact_mod_cast hb'

end PrimeOrderRationalValues
