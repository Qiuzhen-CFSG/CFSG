module
public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.Diagonal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Multiplicity

/-!
# Bounding the PSU₄ order through the determinant kernel

For a coefficient field of order q, the determinant kernel in GL₄ has order
`q^6 (q^2−1) (q^3−1) (q^4−1)`. This follows directly from the GL cardinality
formula and determinant surjectivity. The actual projective SU image has
order dividing that kernel order: SU is a subgroup of the kernel and maps
surjectively onto its projective image.

For an odd prime r dividing q−1, lifting the exponent computes the r-valuation
of this bound as `3*v_r(q−1) + v_r(3)`. The extra factor three is supplied by
the coordinate cycle in `Geometry`. This avoids a full SU order formula.
The determinant argument follows `PSL3Three/Cardinality`; the application is
the covering-kernel step of Aschbacher–Smith A.2.17, printed p.39, under the
cover conventions I.1.1–I.1.4, printed pp.407–408. Here q is the coefficient
field order, hence p² in the unitary application.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
variable {F : Type*} [Field F] [Finite F]

/-- The degree-four determinant kernel order over an arbitrary finite field. -/
theorem card_detKernel_four :
    Nat.card (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker =
      Nat.card F ^ 6 * (Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1) *
        (Nat.card F ^ 4 - 1) := by
  let : Fintype F := Fintype.ofFinite F
  have h := (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective,
    Subgroup.card_top, Nat.card_units, card_GL_field] at h
  simp only [← Nat.card_eq_fintype_card, Fin.prod_univ_succ, Fin.val_zero,
    Fin.val_succ, pow_zero, Nat.zero_add, Fin.prod_univ_zero, mul_one, pow_one] at h
  let q := Nat.card F
  change _ * (q - 1) = (q ^ 4 - 1) * ((q ^ 4 - q) * ((q ^ 4 - q ^ 2) * (q ^ 4 - q ^ 3))) at h
  have h1 : q ^ 4 - q = q * (q ^ 3 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 4 - q ^ 2 = q ^ 2 * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h3 : q ^ 4 - q ^ 3 = q ^ 3 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2, h3] at h
  have hprod : (q ^ 4 - 1) * (q * (q ^ 3 - 1) *
      (q ^ 2 * (q ^ 2 - 1) * (q ^ 3 * (q - 1)))) =
      (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) * (q - 1) := by ring
  rw [hprod] at h
  apply Nat.eq_of_mul_eq_mul_right _ h
  have hq : 1 < q := Finite.one_lt_card
  omega

omit [Finite F] in
/-- The literal projective SU group is a quotient of a subgroup of the determinant kernel. -/
theorem card_projective_dvd_detKernel (J : HermitianForm 4 F) :
    Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) ∣
      Nat.card (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker := by
  apply (Subgroup.card_dvd_of_surjective (ProjectiveKernel.project J)
    (ProjectiveKernel.project_surjective J)).trans
  have hle : J.specialSubgroup ≤ (GeneralLinearGroup.det : GL (Fin 4) F →* Fˣ).ker := by
    intro A hA
    exact ((J.mem_specialSubgroup_iff A).mp hA).2
  exact Subgroup.card_dvd_of_le hle

/-- The exact odd-primary valuation of the determinant-kernel order. -/
theorem valuation_detKernel_order {q r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    (hq : 1 < q) (hd : r ∣ q - 1) :
    padicValNat r (q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) =
      3 * padicValNat r (q - 1) + padicValNat r 3 := by
  have hr := (Fact.out : r.Prime)
  have hrOdd : Odd r := hr.odd_of_ne_two hr2
  have hqr : ¬ r ∣ q := by
    intro he
    have h : r ∣ 1 := by
      convert Nat.dvd_sub he hd using 1
      omega
    exact hr.not_dvd_one h
  have hq0 : q ≠ 0 := by omega
  have hpow (n : ℕ) (hn : n ≠ 0) : q ^ n - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (one_lt_pow₀ hq hn)
  have h2 := hpow 2 (by decide)
  have h3 := hpow 3 (by decide)
  have h4 := hpow 4 (by decide)
  have h6 : q ^ 6 ≠ 0 := pow_ne_zero _ hq0
  have hv (n : ℕ) (hn : n ≠ 0) :
      padicValNat r (q ^ n - 1) = padicValNat r (q - 1) + padicValNat r n := by
    simpa only [one_pow] using padicValNat.pow_sub_pow hrOdd hq hd hqr hn
  have hnr2 : ¬ r ∣ 2 := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
  have hv2 : padicValNat r 2 = 0 := padicValNat.eq_zero_of_not_dvd hnr2
  have hv4 : padicValNat r 4 = 0 := by
    change padicValNat r (2 ^ 2) = 0
    rw [padicValNat.pow, hv2, mul_zero]
  rw [padicValNat.mul (mul_ne_zero (mul_ne_zero h6 h2) h3) h4,
    padicValNat.mul (mul_ne_zero h6 h2) h3, padicValNat.mul h6 h2,
    padicValNat.pow, padicValNat.eq_zero_of_not_dvd hqr, hv 2 (by decide),
    hv 3 (by decide), hv 4 (by decide), hv2, hv4]
  omega

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic
