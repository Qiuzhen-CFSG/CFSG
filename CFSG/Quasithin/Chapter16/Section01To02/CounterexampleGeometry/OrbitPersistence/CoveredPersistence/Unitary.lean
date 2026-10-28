module
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.CoveredPersistence.ModelAlternatives
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Divisibility by three for the unitary endpoint

Transport the given Hermitian form to a standard form, calculate its fixed
field, and apply the checked PSU₃ order formula. Both factors q³+1 and q²−1
supply the factor three when the scalar quotient has order three. No
simplicity theorem or independent classification of unitary groups is used.

This excludes the endpoint in Aschbacher–Smith 16.1.7(3b) from the covered
Suzuki case of 16.2.6, printed pp.1172–1174.
-/

public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
open BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter

private theorem three_dvd_unitary_order (q : ℕ) (hq : 1 ≤ q) (hthree : ¬ 3 ∣ q) :
    3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hsq : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h <;> rw [h]
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
  have hd2 : 3 ∣ q ^ 2 - 1 := by omega
  rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (q + 1)) with hg | hg
  · rw [hg, Nat.div_one]
    exact dvd_mul_of_dvd_right hd2 _
  · rw [hg]
    have hplus : 3 ∣ q + 1 := hg ▸ Nat.gcd_dvd_right 3 (q + 1)
    have hmod2 : q % 3 = 2 := by omega
    have hcube : q ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hmod2]
    have hd3 : 3 ∣ q ^ 3 + 1 := by omega
    have hprod : 3 * 3 ∣ (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) :=
      Nat.mul_dvd_mul (dvd_mul_of_dvd_left hd3 _) hd2
    exact (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right hd2 _)).mpr hprod

/-- The required unitary endpoint has order divisible by three for every
nondegenerate Hermitian form with the specified finite-field involution. -/
theorem unitaryThree : UnitaryThreeInput := by
  intro F hF hfin J n hn hcard hconj
  have hfixed : Nat.card {x : F // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega)
      hcard hconj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J (2 ^ n) hcard hfixed
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨_, _, _, _, _, _, _, _, horder, _⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J)
      (2 ^ n) hcard hfixed rfl
  rw [horder]
  apply three_dvd_unitary_order _ (Nat.one_le_pow _ _ (by decide))
  exact fun h => (by norm_num : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence
end
