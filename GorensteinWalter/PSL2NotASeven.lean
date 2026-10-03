module
public import GorensteinWalter.PSL2Cardinality
public import Mathlib.Tactic

/-!
# Odd PSL2 is not alternating seven

The order of PSL2 over an odd finite field never equals the order of A7.
The formula q(q^2-1)/2=2520 would give q(q^2-1)=5040, forcing q at most17;
the remaining integer range has no solution. Hence no such groups are
isomorphic, including the field-order-three case.

This exact order obstruction was extracted from the Gorenstein--Walter
Section3 layer argument for reuse in the arbitrary-section Dickson proof
required by ABG II.3 Lemma2, article p24. Its existing public name and
statement are preserved and reexported by the original module.
-/

namespace GorensteinWalter
universe u

/-- Odd `PSL₂(K)` is never isomorphic to `A₇`. -/
public theorem psl2_ne_a7
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty (PSL2 K ≃* alternatingGroup (Fin 7))) : False := by
  classical
  rcases e with ⟨e⟩
  let q : ℕ := Nat.card K
  have hqpos : 0 < q := Nat.card_pos
  have hKodd : Odd q := by
    dsimp [q]
    rcases hK with ⟨p, n, _hp, hpodd, _hn, hcard⟩
    rw [hcard]
    exact hpodd.pow
  have hdvd2 : 2 ∣ q * (q ^ 2 - 1) := by
    have hEven : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hKodd.pow odd_one
    exact dvd_mul_of_dvd_right hEven.two_dvd _
  have hcardPSL : Nat.card (PSL2 K) = q * (q ^ 2 - 1) / 2 :=
    by simpa [q] using psl2_card_formula K hK
  have hcardA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hEq : q * (q ^ 2 - 1) / 2 = 2520 := by
    rw [← hcardPSL]
    rw [Nat.card_congr e.toEquiv, hcardA]
  have hEq' : q * (q ^ 2 - 1) = 2 * 2520 := by
    rw [← Nat.div_eq_iff_eq_mul_right (by norm_num) hdvd2]
    exact hEq
  have hEq'' : q * (q ^ 2 - 1) = 5040 := by
    norm_num at hEq'
    exact hEq'
  have hqle : q ≤ 17 := by
    by_contra hnot
    have hge : 18 ≤ q := by omega
    have hqsq_pos : 0 < q ^ 2 := pow_pos hqpos 2
    have h1 : 1 ≤ q ^ 2 := Nat.succ_le_of_lt hqsq_pos
    have hz : (q : ℤ) * ((q : ℤ) ^ 2 - 1) = 5040 := by
      have hsq : (q : ℤ) ^ 2 = (q ^ 2 : ℕ) := by norm_num
      rw [hsq]
      have hcast : ((q ^ 2 : ℕ) : ℤ) - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) :=
        (Int.ofNat_sub h1).symm
      rw [hcast]
      exact_mod_cast hEq''
    have hprod : (18 : ℤ) * (18 ^ 2 - 1) ≤
        (q : ℤ) * ((q : ℤ) ^ 2 - 1) := by
      nlinarith [sq_nonneg (q : ℤ)]
    norm_num at hprod
    omega
  interval_cases q <;> norm_num at hEq''

end GorensteinWalter
