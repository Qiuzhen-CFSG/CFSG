module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime.SplitTorus
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Torus
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
/-!
# The split-primary bound from the isotropic-point stabilizer

The first-vector stabilizer has a Heisenberg kernel and an actual SL₂ quotient
on the perpendicular plane. The first-coordinate character of the full point
stabilizer is onto Fˣ, with that vector stabilizer as kernel. These literal maps
give the point stabilizer order q⁶(q²−1)² when |F| = q² and the fixed field has
order q. For every odd prime p dividing q−1 its valuation is exactly 2 vₚ(q−1).

Consequently a prime-to-p point index gives the required ambient primary-order
bound and the split-torus covering-kernel exclusion. The final two applications
accept the expected geometric index (q³+1)(q²+1) and prove its coprimality. The
geometric index itself remains a separate counting obligation: this module does
not assert the unconditional ambient bound or covering exclusion.

Source: Aschbacher–Smith I.1.1–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1. The vector-stabilizer calculation uses the matrix maps in
`ClassicalUnitary.UnitaryFourPointLocal` and `UnitaryFourPointQuotient`.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient UnitaryFourSylow
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.UnitaryQuadratic.PairedTorus
public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
namespace SplitPrimaryBound
variable {F : Type*} [Field F] [Finite F]
section CharTwo
variable [CharP F 2] (σ : F ≃+* F) (hσ : Function.Involutive σ)

/-- Order of the stabilizer of the first isotropic vector. -/
theorem local_card : Nat.card (localSU F (form F σ hσ)) =
    Nat.card F ^ 2 * Nat.card (FixedBy.subfield F σ) ^ 2 *
      (Nat.card (FixedBy.subfield F σ) ^ 2 - 1) := by
  have h := (middleSL F σ hσ).ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (middleSL_surjective F σ hσ),
    Subgroup.card_top, middleSL_ker, radical_card,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at h
  exact h.symm.trans (by ring)

omit [CharP F 2] in
private theorem scalar_surjective :
    Function.Surjective (pointScalar F (form F σ hσ)).toHomUnits := by
  intro a
  let b := torusLift F σ hσ a 1
  refine ⟨⟨b.val, b.property.1⟩, ?_⟩
  apply Units.ext
  change b.val.val.val 0 0 = (a : F)
  rw [← torusCharacter_fst_val]
  exact congrArg (fun x : Fˣ × (FixedBy.subfield F σ)ˣ => (x.1 : F))
    (torusCharacter_lift F σ hσ a 1)

/-- Order of the full isotropic-point stabilizer via its scalar character. -/
theorem point_card : Nat.card (pointParabolicSU F (form F σ hσ)) =
    Nat.card F ^ 2 * Nat.card (FixedBy.subfield F σ) ^ 2 *
      (Nat.card (FixedBy.subfield F σ) ^ 2 - 1) * (Nat.card F - 1) := by
  have h := (pointScalar F (form F σ hσ)).toHomUnits.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (scalar_surjective σ hσ),
    Subgroup.card_top, Nat.card_units, MonoidHom.ker_toHomUnits,
    ← localSU_subgroupOf_eq_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (localSU_le_pointParabolicSU F (form F σ hσ))).toEquiv,
    local_card] at h
  exact h.symm
end CharTwo

/-- The literal point parabolic in binary SU₄ has order q⁶(q²−1)². -/
theorem binary_point_card (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nat.card (pointParabolicSU F (UnitaryFourFormTransport.standardForm J)) =
      (2 ^ n) ^ 6 * ((2 ^ n) ^ 2 - 1) ^ 2 := by
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n hn hcard
  have hf : Nat.card (FixedBy.subfield F J.conj) = 2 ^ n :=
    UnitaryFourFormTransport.fixed_card J n hn hcard hconj
  rw [point_card, hcard, hf]
  ring

private theorem not_dvd_parameter {q p : ℕ} [Fact p.Prime]
    (hq : 1 < q) (hd : p ∣ q - 1) : ¬ p ∣ q := by
  intro hpq
  have h : p ∣ 1 := by
    convert Nat.dvd_sub hpq hd using 1
    omega
  exact (Fact.out : p.Prime).not_dvd_one h

private theorem not_dvd_add_one {q p : ℕ} [Fact p.Prime]
    (hq : 1 < q) (hp : p ≠ 2) (hd : p ∣ q - 1) : ¬ p ∣ q + 1 := by
  intro hplus
  have h : p ∣ 2 := by
    convert Nat.dvd_sub hplus hd using 1
    omega
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h)

/-- All p-primary factors of the point stabilizer come from its two split factors. -/
theorem point_order_valuation {q p : ℕ} [Fact p.Prime]
    (hq : 1 < q) (hp : p ≠ 2) (hd : p ∣ q - 1) :
    padicValNat p (q ^ 6 * (q ^ 2 - 1) ^ 2) = 2 * padicValNat p (q - 1) := by
  have hq0 : q ≠ 0 := by omega
  have hm : q - 1 ≠ 0 := by omega
  have he : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    simpa only [one_pow] using Nat.sq_sub_sq q 1
  rw [he, padicValNat.mul (pow_ne_zero _ hq0)
    (pow_ne_zero _ (mul_ne_zero (by omega) hm)), padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd (not_dvd_parameter hq hd), mul_zero, zero_add,
    padicValNat.pow, padicValNat.mul (by omega) hm,
    padicValNat.eq_zero_of_not_dvd (not_dvd_add_one hq hp hd), zero_add]

/-- The point stabilizer has no additional factor of p beyond the paired torus. -/
theorem point_order_bound {q p : ℕ} [Fact p.Prime]
    (hq : 1 < q) (hp : p ≠ 2) (hd : p ∣ q - 1) :
    ¬ p * primaryExponent q p ^ 2 ∣ q ^ 6 * (q ^ 2 - 1) ^ 2 := by
  have hq0 : q ≠ 0 := by omega
  have hm : q ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (one_lt_pow₀ hq (by decide : 2 ≠ 0))
  have he : p * primaryExponent q p ^ 2 = p ^ (2 * padicValNat p (q - 1) + 1) := by
    rw [primaryExponent, Nat.factorization_def _ (Fact.out : p.Prime), ← pow_mul,
      pow_succ, mul_comm p, Nat.mul_comm (padicValNat p (q - 1)) 2]
  rw [he, padicValNat_dvd_iff_le (mul_ne_zero (pow_ne_zero _ hq0) (pow_ne_zero _ hm)),
    point_order_valuation hq hp hd]
  omega

/-- The proposed point index is prime to every odd divisor of q−1. -/
theorem point_index_not_dvd {q p : ℕ} [Fact p.Prime]
    (hq : 1 < q) (hp : p ≠ 2) (hd : p ∣ q - 1) :
    ¬ p ∣ (q ^ 3 + 1) * (q ^ 2 + 1) := by
  have he (k : ℕ) (hk : k ≠ 0) : ¬ p ∣ q ^ k + 1 := by
    apply not_dvd_add_one (one_lt_pow₀ hq hk) hp
    exact hd.trans (by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 k)
  exact fun h => ((Fact.out : p.Prime).dvd_mul.mp h).elim
    (he 3 (by decide)) (he 2 (by decide))

end SplitPrimaryBound

variable {F : Type*} [Field F] [Finite F]

/-- Prime-to-p point index suffices for the full ambient primary-order bound. -/
theorem split_primary_card_bound_of_point_index
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n - 1)
    (hi : ¬ p ∣ (pointParabolicSU F
      (UnitaryFourFormTransport.standardForm J)).index) :
    ¬ p * primaryExponent (2 ^ n) p ^ 2 ∣ Nat.card (Standard J) := by
  let P := pointParabolicSU F (UnitaryFourFormTransport.standardForm J)
  have hc : (p * primaryExponent (2 ^ n) p ^ 2).Coprime P.index := by
    have h : p.Coprime P.index := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hi
    exact Nat.coprime_mul_iff_left.mpr ⟨h, (h.pow_left _).pow_left _⟩
  intro hdiv
  have hb := SplitPrimaryBound.point_order_bound
    (one_lt_pow₀ (by decide : 1 < 2) hn.ne') hp hd
  apply hb
  rw [← SplitPrimaryBound.binary_point_card J n hn hcard hconj]
  apply hc.dvd_mul_right.mp
  rwa [P.card_mul_index]

/-- The geometric point count discharges the prime-index premise. -/
theorem split_primary_card_bound_of_point_index_eq
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n - 1)
    (hi : (pointParabolicSU F (UnitaryFourFormTransport.standardForm J)).index =
      ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 + 1)) :
    ¬ p * primaryExponent (2 ^ n) p ^ 2 ∣ Nat.card (Standard J) := by
  apply split_primary_card_bound_of_point_index J n hn hcard hconj hp hd
  rw [hi]
  exact SplitPrimaryBound.point_index_not_dvd
    (one_lt_pow₀ (by decide : 1 < 2) hn.ne') hp hd

/-- The actual cover application, with only the geometric point index still explicit. -/
theorem not_dvd_kernel_of_split_point_index
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n - 1)
    (hi : ¬ p ∣ (pointParabolicSU F
      (UnitaryFourFormTransport.standardForm J)).index)
    {E : Type*} [Group E] [Finite E] (d : PerfectCentralCovering.Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker :=
  not_dvd_kernel_of_split_card_bound J n hn hcard hconj hp
    (split_primary_card_bound_of_point_index J n hn hcard hconj hp hd hi) d

/-- Applying the geometric point count to the literal covering map. -/
theorem not_dvd_kernel_of_split_point_index_eq
    (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hd : p ∣ 2 ^ n - 1)
    (hi : (pointParabolicSU F (UnitaryFourFormTransport.standardForm J)).index =
      ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 + 1))
    {E : Type*} [Group E] [Finite E] (d : PerfectCentralCovering.Cover E (Standard J)) :
    ¬ p ∣ Nat.card d.toMonoidHom.ker :=
  not_dvd_kernel_of_split_card_bound J n hn hcard hconj hp
    (split_primary_card_bound_of_point_index_eq J n hn hcard hconj hp hd hi) d

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.EvenFourClosure.OddPrime
