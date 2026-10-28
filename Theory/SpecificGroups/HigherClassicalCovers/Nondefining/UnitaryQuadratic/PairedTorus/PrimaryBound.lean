module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus.Coefficients
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality

/-!
# The split-prime part of the actual PSU₄ order

For an odd prime `r` dividing `p - 1`, the exact order of the special unitary
matrix group in dimension four has `r`-factor exactly
`r ^ (2 * vᵣ(p - 1))`.  The projective image is a quotient image of that
matrix group, so its order cannot contain one further factor of `r` beyond the
paired torus square.

The source order calculation is the checked first-column count in
`ClassicalUnitary.UnitaryFourCardinality`.  This module only applies the
counting result and elementary factorization; it does not use a natural-cover,
multiplier, simplicity or universality assertion.

Source: Aschbacher--Smith A.2.17, printed p.39, with the order convention from
GLS3 §6.1.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open OddFourRanks.Defining ProjectiveKernel

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus

private theorem hpm_of_dvd {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hd : r ∣ p - 1) : (p : ZMod r) = 1 := by
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hz := (ZMod.natCast_eq_zero_iff (p - 1) r).mpr hd
  rw [Nat.cast_sub hp1] at hz
  simpa using sub_eq_zero.mp hz

private theorem absurd_two {r : ℕ} [Fact r.Prime] (hr : r ≠ 2)
    (htwo : (2 : ZMod r) = 0) : False := by
  apply hr
  apply (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime r) Nat.prime_two).mp
  exact (ZMod.natCast_eq_zero_iff 2 r).mp htwo

private theorem not_dvd_plus_one {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hd : r ∣ p - 1) (hr : r ≠ 2) : ¬ r ∣ p + 1 := by
  have hpm := hpm_of_dvd hd
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (p + 1) r).mpr h
  push_cast at hz
  have htwo' : (1 + 1 : ZMod r) = 0 := by simpa [hpm] using hz
  exact absurd_two hr (by simpa only [one_add_one_eq_two] using htwo')

private theorem not_dvd_sq_add_one {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hd : r ∣ p - 1) (hr : r ≠ 2) : ¬ r ∣ p ^ 2 + 1 := by
  have hpm := hpm_of_dvd hd
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (p ^ 2 + 1) r).mpr h
  push_cast at hz
  have htwo' : (1 + 1 : ZMod r) = 0 := by simpa [hpm] using hz
  exact absurd_two hr (by simpa only [one_add_one_eq_two] using htwo')

private theorem not_dvd_cube_add_one {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hd : r ∣ p - 1) (hr : r ≠ 2) : ¬ r ∣ p ^ 3 + 1 := by
  have hpm := hpm_of_dvd hd
  intro h
  have hz := (ZMod.natCast_eq_zero_iff (p ^ 3 + 1) r).mpr h
  push_cast at hz
  have htwo' : (1 + 1 : ZMod r) = 0 := by simpa [hpm] using hz
  exact absurd_two hr (by simpa only [one_add_one_eq_two] using htwo')

private theorem special_order_factorization {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hp3 : 3 < p) (hr : r ≠ 2) (hd : r ∣ p - 1) :
    (p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1)).factorization r =
      2 * (p - 1).factorization r := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hp1 : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hpm0 : p - 1 ≠ 0 := (Nat.sub_ne_zero_iff_lt).2 (by omega)
  have hplus0 : p + 1 ≠ 0 := by omega
  have hsqsub0 : p ^ 2 - 1 ≠ 0 := by
    apply (Nat.sub_ne_zero_iff_lt).2
    exact one_lt_pow₀ (by omega) (by decide)
  have hcubeplus0 : p ^ 3 + 1 ≠ 0 := by positivity
  have hsqplus0 : p ^ 2 + 1 ≠ 0 := by positivity
  have hfour0 : p ^ 4 - 1 ≠ 0 := by
    apply (Nat.sub_ne_zero_iff_lt).2
    exact one_lt_pow₀ (by omega) (by decide)
  have hn_p : ¬ r ∣ p := by
    have hcopsub : Nat.Coprime (p - 1) p :=
      (Nat.coprime_self_sub_left hp1).2 (Nat.coprime_one_left p)
    exact (Fact.out : Nat.Prime r).coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hd hcopsub)
  have hn_plus : ¬ r ∣ p + 1 := not_dvd_plus_one hd hr
  have hn_sqplus : ¬ r ∣ p ^ 2 + 1 := not_dvd_sq_add_one hd hr
  have hn_cubeplus : ¬ r ∣ p ^ 3 + 1 := not_dvd_cube_add_one hd hr
  have hn_p6 : (p ^ 6).factorization r = 0 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.factorization_eq_zero_of_not_dvd hn_p, mul_zero]
  have hv_sqsub : (p ^ 2 - 1).factorization r = (p - 1).factorization r := by
    have he : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      calc
        p ^ 2 - 1 = p ^ 2 - 1 ^ 2 := by norm_num
        _ = (p - 1) * (p + 1) := by rw [Nat.sq_sub_sq]; ac_rfl
    rw [he, Nat.factorization_mul hpm0 hplus0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hn_plus, add_zero]
  have hv_cube : (p ^ 3 + 1).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hn_cubeplus
  have hv_four : (p ^ 4 - 1).factorization r = (p - 1).factorization r := by
    have he : p ^ 4 - 1 = (p ^ 2 - 1) * (p ^ 2 + 1) := by
      calc
        p ^ 4 - 1 = (p ^ 2) ^ 2 - 1 ^ 2 := by ring_nf
        _ = (p ^ 2 - 1) * (p ^ 2 + 1) := by rw [Nat.sq_sub_sq]; ac_rfl
    rw [he, Nat.factorization_mul hsqsub0 hsqplus0, Finsupp.add_apply,
      hv_sqsub, Nat.factorization_eq_zero_of_not_dvd hn_sqplus, add_zero]
  rw [show p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) =
      p ^ 6 * ((p ^ 2 - 1) * ((p ^ 3 + 1) * (p ^ 4 - 1))) by ring]
  rw [Nat.factorization_mul (pow_ne_zero _ hp0) (by positivity),
    Nat.factorization_mul hsqsub0 (by positivity),
    Nat.factorization_mul hcubeplus0 hfour0]
  simp only [Finsupp.add_apply, hn_p6, hv_sqsub, hv_cube, hv_four, zero_add]
  omega

/-- The actual projective PSU₄ image has no extra `r` beyond the paired
coefficient square when `r` is an odd split prime of `p - 1`. -/
theorem not_dvd_primary_card_bound
    {F : Type*} [Field F] [Finite F] {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (J : HermitianForm 4 F) (hF : Nat.card F = p ^ 2)
    (hc : ∀ x, J.conj x = x ^ p) (hr2 : r ≠ 2) (hrp : r ≠ p)
    (hd : r ∣ p - 1) :
    ¬ r * primaryExponent p r ^ 2 ∣
      Nat.card (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J)) := by
  intro hdiv
  have hp3 : 3 < p := by
    have hp2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    have hpos : 0 < p - 1 := by omega
    have hrle : r ≤ p - 1 := Nat.le_of_dvd hpos hd
    have hr2le : 2 ≤ r := (Fact.out : Nat.Prime r).two_le
    have hr3 : 3 ≤ r := by omega
    omega
  have hhc : ∀ x, (hyperbolicForm J).conj x = x ^ p := by
    intro x
    simpa [hyperbolicForm] using hc x
  have hsu := Theory.SpecificGroups.ClassicalUnitary.UnitaryFourCardinality.card_specialSubgroup
    (hyperbolicForm J) hp3 hF hhc
  have hproj : Nat.card (ProjectiveSpecialUnitaryMatrixGroup (hyperbolicForm J)) ∣
      p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) := by
    change Nat.card ((hyperbolicForm J).specialSubgroup.map ProjGenLinGroup.mk) ∣ _
    rw [← hsu]
    exact (hyperbolicForm J).specialSubgroup.card_map_dvd ProjGenLinGroup.mk
  have hD : r * primaryExponent p r ^ 2 ∣
      p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) := hdiv.trans hproj
  have hv : r ^ (2 * (p - 1).factorization r + 1) ∣
      p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) := by
    have he : r * primaryExponent p r ^ 2 =
        r ^ (2 * (p - 1).factorization r + 1) := by
      simpa [primaryExponent] using (show r * (r ^ (p - 1).factorization r) ^ 2 =
        r ^ (2 * (p - 1).factorization r + 1) by
          rw [pow_two, ← pow_add, mul_comm r, ← pow_succ]
          congr 1
          omega)
    rwa [he] at hD
  have hsq0 : p ^ 2 - 1 ≠ 0 := (Nat.sub_ne_zero_iff_lt).2
    (one_lt_pow₀ (by omega) (by decide))
  have hfour0 : p ^ 4 - 1 ≠ 0 := (Nat.sub_ne_zero_iff_lt).2
    (one_lt_pow₀ (by omega) (by decide))
  have hS0 : p ^ 6 * (p ^ 2 - 1) * (p ^ 3 + 1) * (p ^ 4 - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero) hsq0)
      (by positivity)) hfour0
  have hle := ((Fact.out : Nat.Prime r).pow_dvd_iff_le_factorization hS0).mp hv
  rw [special_order_factorization hp3 hr2 hd] at hle
  omega

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus
