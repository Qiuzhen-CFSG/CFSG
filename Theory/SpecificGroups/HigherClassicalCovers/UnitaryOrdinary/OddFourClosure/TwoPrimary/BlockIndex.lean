module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.BlockModel
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary.Splitting
public import Theory.AtlasPort.LinearGroups.SL2Order
import Mathlib.Tactic.Ring

/-!
# Counting reduction for the unitary block-pair index

The injective block model has range order
`2 * q² * (q² - 1)² * (q + 1)`, independently of its action. The expected
SU₄ order factors as that number times
`q⁴ * (q² - q + 1) * ((q² + 1) / 2)`. This last factor is odd for every
odd q. Thus even a divisibility bound by the special unitary order suffices
for odd index. The literal range section and transfer then exclude a
perfect central cover of degree two, and prime-degree reduction applies
the same calculation to arbitrary finite kernels.

The ambient special-unitary order bound is an explicit premise here;
its geometric counting proof is still required. These are counting and
transfer reductions, not the unconditional Mersenne source theorem.

Source: the local subgroup calculation supporting Aschbacher--Smith
I.1.4(3), printed p.408 of `refs/quasithin.pdf`, and GLS3 §6.1. The rank-one
count is the checked `Atlas.card_sl_two`.
-/

public section

open BenderSuzuki.MatrixGroups PerfectCentralCovering
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary

/-- Count the literal range using the injective semidirect-product map. -/
theorem card_blockModel_range {F : Type*} [Field F] (J : HermitianForm 4 F)
    {q : ℕ} [Fact q.Prime] (m : BlockModel J q) :
    Nat.card m.inclusion.range = 2 * q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + 1) := by
  rw [← Nat.card_congr (MonoidHom.ofInjective m.injective).toEquiv,
    SemidirectProduct.card, Nat.card_prod, DihedralGroup.nat_card]
  have hr : Nat.card (RankOne q) = q * (q ^ 2 - 1) := by
    simpa only [RankOne, Nat.card_zmod] using (Atlas.card_sl_two (F := ZMod q))
  rw [hr]
  ring

private theorem odd_half_sq_add_one {q : ℕ} (hq : Odd q) : Odd ((q ^ 2 + 1) / 2) := by
  obtain ⟨k, rfl⟩ := hq.exists_bit1
  have he : ((2 * k + 1) ^ 2 + 1) / 2 = 2 * (k ^ 2 + k) + 1 := by
    apply Nat.div_eq_of_eq_mul_left (by decide : 0 < 2)
    ring
  rw [he]
  exact odd_two_mul_add_one _

private theorem double_half_sq_add_one {q : ℕ} (hq : Odd q) :
    2 * ((q ^ 2 + 1) / 2) = q ^ 2 + 1 :=
  Nat.mul_div_cancel' (even_iff_two_dvd.mp hq.pow.add_one)

private theorem unitary_order_factorization {q : ℕ} (hq : 1 ≤ q) (ho : Odd q) :
    q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1) =
      (2 * q ^ 2 * (q ^ 2 - 1) ^ 2 * (q + 1)) *
        (q ^ 4 * (q ^ 2 - q + 1) * ((q ^ 2 + 1) / 2)) := by
  have h2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hc : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have he := Nat.sub_add_cancel hq2
    nlinarith
  have h4 : q ^ 4 - 1 = (q ^ 2 - 1) * (q ^ 2 + 1) := by
    have he := Nat.sub_add_cancel h2
    have he4 : 1 ≤ q ^ 4 := one_le_pow₀ hq
    have he' := Nat.sub_add_cancel he4
    nlinarith [sq_nonneg (q ^ 2)]
  rw [hc, h4]
  conv_lhs => rw [← double_half_sq_add_one ho]
  ring

private theorem odd_unitary_index {q : ℕ} (hq : Odd q) :
    Odd (q ^ 4 * (q ^ 2 - q + 1) * ((q ^ 2 + 1) / 2)) :=
  (hq.pow.mul (hq.pow.tsub_odd hq).add_one).mul (odd_half_sq_add_one hq)

universe u
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 4 F)
variable {q : ℕ} [Fact q.Prime]

/-- The exact SU₄ order gives the explicit block-pair index. -/
theorem index_blockModel_of_card_special (hq : 3 < q) (m : BlockModel J q)
    (horder : Nat.card J.specialSubgroup =
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) :
    m.inclusion.range.index =
      q ^ 4 * (q ^ 2 - q + 1) * ((q ^ 2 + 1) / 2) := by
  have ho : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := m.inclusion.range))
  rw [m.inclusion.range.card_mul_index, card_blockModel_range,
    ← unitary_order_factorization (by omega) ho]
  exact horder

/-- A divisor of the special-unitary order has no extra two-part beyond
the block range. The ambient divisibility premise remains to be proved. -/
theorem odd_index_blockModel_of_card_dvd (hq : 3 < q) (m : BlockModel J q)
    (horder : Nat.card J.specialSubgroup ∣
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) :
    Odd m.inclusion.range.index := by
  have ho : Odd q := (Fact.out : q.Prime).odd_of_ne_two (by omega)
  apply (odd_unitary_index ho).of_dvd_nat
  apply Nat.dvd_of_mul_dvd_mul_left (Nat.card_pos (α := m.inclusion.range))
  rwa [m.inclusion.range.card_mul_index, card_blockModel_range,
    ← unitary_order_factorization (by omega) ho]

/-- The counting bound supplies the odd-index premise of the actual
block-model section and perfect-cover transfer application. -/
theorem noPrimeKernel_of_blockModel_card_dvd (hq : 3 < q) (m : BlockModel J q)
    (horder : Nat.card J.specialSubgroup ∣
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1)) : NoPrimeKernel J 2 := by
  intro E _ _ f hcard
  obtain ⟨s, hs⟩ := exists_section_on_block_model J hq m f.toMonoidHom
    f.surjective f.ker_le_center hcard
  exact not_dvd_card_kernel_of_section f m.inclusion.range
    (odd_index_blockModel_of_card_dvd J hq m horder).not_two_dvd_nat s hs
    (hcard ▸ dvd_rfl)

/-- The same conditional counting result excludes two from every finite
perfect covering kernel, including kernels of mixed prime order. -/
theorem not_dvd_card_kernel_of_blockModel_card_dvd (hq : 3 < q) (m : BlockModel J q)
    (horder : Nat.card J.specialSubgroup ∣
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 + 1) * (q ^ 4 - 1))
    {E : Type u} [Group E] [Finite E] (f : Cover E J.specialSubgroup) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  f.not_dvd_card_kernel_of_no_prime_kernel
    (noPrimeKernel_of_blockModel_card_dvd J hq m horder)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddFourClosure.TwoPrimary
