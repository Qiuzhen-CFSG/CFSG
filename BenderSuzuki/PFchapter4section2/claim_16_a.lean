/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFchapter4section2.claim_15_b

namespace BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (16), first clause -/

/-- The characteristic root `beta` generates the coordinate copy of `W`. -/
public theorem claim_16_a
    (E : Type*) [Field E] [Finite E] [CharP E 2] (W : Subgroup Eˣ) (m : ℕ)
    (zeta alpha beta : E) (zetaUnit betaUnit : Eˣ) (u : ℕ → E)
    (hzeta_coe : (zetaUnit : E) = zeta)
    (hbeta_coe : (betaUnit : E) = beta)
    (hzeta_generator : Subgroup.closure ({zetaUnit} : Set Eˣ) = W)
    (hWcard : Nat.card W = m)
    (hbeta_mem : betaUnit ∈ W) (hbeta_ne : beta ≠ 0)
    (hroot : beta ^ 2 + alpha * beta + 1 = 0)
    (hu_closed : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      u i = (beta ^ (i - 1) + (beta⁻¹) ^ (i - 1)) /
        (beta ^ i + (beta⁻¹) ^ i))
    (hden : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      beta ^ i + (beta⁻¹) ^ i ≠ 0)
    (huterminal : u (m - 1) = alpha) :
    Subgroup.closure ({betaUnit} : Set Eˣ) = W := by
  have hm_pos : 0 < m := by
    rw [← hWcard]
    exact Nat.card_pos
  have horder_dvd : orderOf betaUnit ∣ m := by
    rw [← hWcard]
    exact W.orderOf_dvd_natCard hbeta_mem
  have horder_le : orderOf betaUnit ≤ m :=
    Nat.le_of_dvd hm_pos horder_dvd
  have horder_pos : 0 < orderOf betaUnit := orderOf_pos betaUnit
  have hm_le_order : m ≤ orderOf betaUnit := by
    by_contra hnot
    have horder_lt : orderOf betaUnit < m := Nat.lt_of_not_ge hnot
    have horder_m1 : orderOf betaUnit ≤ m - 1 := by omega
    have hbeta_pow : beta ^ orderOf betaUnit = 1 := by
      have hunit_pow : (betaUnit : E) ^ orderOf betaUnit = 1 := by
        change ((betaUnit ^ orderOf betaUnit : Eˣ) : E) = ((1 : Eˣ) : E)
        rw [pow_orderOf_eq_one]
      simpa [hbeta_coe] using hunit_pow
    have hbeta_inv_pow : (beta⁻¹) ^ orderOf betaUnit = 1 := by
      rw [inv_pow, hbeta_pow, inv_one]
    apply hden (orderOf betaUnit) horder_pos horder_m1
    rw [hbeta_pow, hbeta_inv_pow]
    exact CharTwo.add_self_eq_zero 1
  have horder : orderOf betaUnit = m :=
    Nat.le_antisymm horder_le hm_le_order
  have hclosure_le : Subgroup.closure ({betaUnit} : Set Eˣ) ≤ W := by
    rw [← Subgroup.zpowers_eq_closure]
    exact Subgroup.zpowers_le.mpr hbeta_mem
  apply Subgroup.eq_of_le_of_card_ge hclosure_le
  rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, horder, hWcard]

end PFchapter4section2
end BenderSuzuki
