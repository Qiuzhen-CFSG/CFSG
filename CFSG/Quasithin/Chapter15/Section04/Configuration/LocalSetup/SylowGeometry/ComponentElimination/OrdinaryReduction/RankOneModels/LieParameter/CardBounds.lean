module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Orders

/-!
# Two-part bounds for the odd rank-one comparison

For odd p, |PSL₂(p)| = p(p²−1)/2. Splitting p modulo four puts every
power of two dividing the group order into p−1 or p+1. Thus 2^n ≤ p+1.
The increasing cubic order numerator then excludes a model whose total
order is too small for its two-part. No recognition from order is used.

These arithmetic comparisons support the model-list intersection in
Aschbacher–Smith, full 1.1.5(3), printed pp.501–503, as used in the proof
of 15.4.20, p.1164. The imported matrix order formula retains its ATLAS
attribution in RankOneModels.Orders and the lower order modules.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
variable {Q : Type*} [Group Q]

/-- The odd PSL₂ order formula without division. -/
theorem odd_card_twice {p : ℕ} (ho : Odd p)
    (h : ClassicalGroup.IsPSL Q 2 p) : Nat.card Q * 2 = p * (p^2-1) := by
  have he := psl_two_card_mul h
  rwa [Nat.gcd_eq_left (even_iff_two_dvd.mp (ho.tsub_odd odd_one))] at he

/-- A two-power dividing an odd PSL₂ order is bounded by the parameter plus one. -/
theorem two_power_dvd_card_le_parameter {p n : ℕ} (ho : Odd p) (hp : 2 ≤ p)
    (hmodel : ClassicalGroup.IsPSL Q 2 p) (hd : 2^n ∣ Nat.card Q) : 2^n ≤ p+1 := by
  have he := odd_card_twice ho hmodel
  have hs : p^2-1+1=p^2 := Nat.sub_add_cancel (by nlinarith)
  obtain ⟨k,hk⟩ := ho
  have hfac : p^2-1 = (p-1)*(p+1) := by
    have hp1 : p-1+1=p := Nat.sub_add_cancel (by omega)
    nlinarith
  rw [hfac] at he
  have hcases : p = 4*(k/2)+1 ∨ p = 4*(k/2)+3 := by omega
  rcases hcases with hpq | hpq
  · have hc : Nat.card Q = (p * (2*(k/2)+1))*(p-1) := by
      apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
      calc
        Nat.card Q * 2 = p * ((p-1)*(p+1)) := he
        _ = _ := by rw [show p+1 = 2*(2*(k/2)+1) by omega]; ring
    have hcop : Nat.Coprime (2^n) (p * (2*(k/2)+1)) := by
      apply Nat.Coprime.pow_left
      apply Nat.coprime_two_left.mpr
      exact (show Odd p from ⟨k,hk⟩).mul ⟨k/2,rfl⟩
    rw [hc] at hd
    have hb := Nat.le_of_dvd (by omega : 0 < p-1) (hcop.dvd_mul_left.mp hd)
    omega
  · have hc : Nat.card Q = (p * (2*(k/2)+1))*(p+1) := by
      apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2)
      calc
        Nat.card Q * 2 = p * ((p-1)*(p+1)) := he
        _ = _ := by rw [show p-1 = 2*(2*(k/2)+1) by omega]; ring
    have hcop : Nat.Coprime (2^n) (p * (2*(k/2)+1)) := by
      apply Nat.Coprime.pow_left
      apply Nat.coprime_two_left.mpr
      exact (show Odd p from ⟨k,hk⟩).mul ⟨k/2,rfl⟩
    rw [hc] at hd
    exact Nat.le_of_dvd (by omega) (hcop.dvd_mul_left.mp hd)

/-- Compare a model order with the least PSL₂ order permitted by its two-part. -/
theorem not_of_two_power_card_bound {p n : ℕ} (ho : Odd p) (hp : 2 ≤ p)
    (hmodel : ClassicalGroup.IsPSL Q 2 p) (hd : 2^n ∣ Nat.card Q)
    (hbound : 2 * Nat.card Q < (2^n-1)*((2^n-1)^2-1)) : False := by
  have hl := two_power_dvd_card_le_parameter ho hp hmodel hd
  have hp' : 2^n-1 ≤ p := by omega
  have hh := Nat.mul_le_mul hp'
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hp' 2) 1)
  have he := odd_card_twice ho hmodel
  omega


/-- A convenient product bound for split characteristic-two model orders. -/
theorem not_of_two_power_order_product {p n b : ℕ} (ho : Odd p) (hp : 2 ≤ p)
    (hmodel : ClassicalGroup.IsPSL Q 2 p) (hd : 2^n ∣ Nat.card Q)
    (hc : Nat.card Q ≤ 2^n*(2^n-1)*b) (hb : 2*b+2 < 2^n) : False := by
  apply not_of_two_power_card_bound ho hp hmodel hd
  let a := 2^n
  have ha : 3 ≤ a := by dsimp [a]; omega
  have hs1 : a-1+1=a := Nat.sub_add_cancel (by omega)
  have he : (a-1)*((a-1)^2-1) = a*(a-1)*(a-2) := by
    have hs : (a-1)^2-1 = a*(a-2) := by
      simpa only [one_pow, hs1, Nat.sub_sub, Nat.reduceAdd] using Nat.sq_sub_sq (a-1) 1
    rw [hs]; ring
  change 2*Nat.card Q < (a-1)*((a-1)^2-1)
  rw [he]
  calc
    2*Nat.card Q ≤ 2*(a*(a-1)*b) := Nat.mul_le_mul_left 2 hc
    _ = a*(a-1)*(2*b) := by ring
    _ < a*(a-1)*(a-2) := Nat.mul_lt_mul_of_pos_left (by dsimp [a]; omega)
      (Nat.mul_pos (by omega) (by omega))

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
