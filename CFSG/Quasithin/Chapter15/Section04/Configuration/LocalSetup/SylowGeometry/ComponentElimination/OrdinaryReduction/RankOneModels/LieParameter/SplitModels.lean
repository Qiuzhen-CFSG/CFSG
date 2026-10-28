module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter.CardBounds
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Excluding the larger split characteristic-two models

For q = 2^f ≥ 4, the orders of PSL₃(q), PSp₄(q), and G₂(q) have
respective two-parts q³, q⁴, and q⁶. Their total orders are too small
for an odd PSL₂ with those two-parts. The PSL₃ scalar divisor is odd;
in characteristic two the symplectic central quotient is identified
with its actual matrix group. The G₂ order is that of the actual
split-octonion automorphism model.

Source: Aschbacher–Smith, full 1.1.5(3), printed pp.501–503, compared in
the proof of 15.4.20, p.1164. The imported linear and G₂ order calculations
retain their ATLAS attribution and license in the lower modules.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
variable {Q : Type*} [Group Q]

private theorem twice_square_lt_pow {q r : ℕ} (hq : 4 ≤ q) (hr : 3 ≤ r) :
    2*(q^2-1)+2 < q^r := by
  have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
  have hh := Nat.mul_lt_mul_of_pos_left (show 2 < q by omega)
    (show 0 < q^2 by positivity)
  have hc : 2*(q^2-1)+2 < q^3 := by nlinarith
  exact hc.trans_le (Nat.pow_le_pow_right (by omega) hr)

/-- Every larger binary PSL₃ is excluded by its two-part and total order. -/
theorem not_linear_three {p f : ℕ} (ho : Odd p) (hp : 2 ≤ p) (hf : 2 ≤ f)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hmodel : ClassicalGroup.IsPSL Q 3 (2^f)) :
    False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let q := 2^f
  have hq : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv, hF] at hc
  change Nat.card Q * Nat.gcd 3 (q-1) * (q-1) = _ at hc
  simp only [Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero,
    pow_one, Nat.zero_add, Nat.reduceAdd, Fin.prod_univ_zero, mul_one] at hc
  change Nat.card Q * Nat.gcd 3 (q-1) * (q-1) =
    (q^3-1)*((q^3-q)*(q^3-q^2)) at hc
  have hfact1 : q^3-q = q*(q^2-1) := by
    have hs : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1; ring
  have hfact2 : q^3-q^2 = q^2*(q-1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]; congr 1
  have hc' : Nat.card Q * Nat.gcd 3 (q-1) = q^3*(q^3-1)*(q^2-1) := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q-1 by omega)
    calc
      _ = (q^3-1)*((q^3-q)*(q^3-q^2)) := hc
      _ = _ := by rw [hfact1, hfact2]; ring
  have hd : q^3 ∣ Nat.card Q := by
    have hcop : Nat.Coprime (q^3) (Nat.gcd 3 (q-1)) := by
      apply Nat.Coprime.pow_left
      apply Nat.Coprime.pow_left
      exact (show Nat.Coprime 2 3 by decide).of_dvd_right (Nat.gcd_dvd_left 3 (q-1))
    apply hcop.dvd_mul_right.mp
    rw [hc']
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  apply not_of_two_power_order_product (n := f*3) (b := q^2-1) ho hp hodd
  · simpa only [pow_mul] using hd
  · rw [pow_mul]
    exact (Nat.le_mul_of_pos_right _ (Nat.gcd_pos_of_pos_left _ (by decide))).trans_eq hc'
  · simpa only [pow_mul] using twice_square_lt_pow hq (by decide : 3 ≤ 3)

/-- The four-dimensional binary symplectic models have incompatible two-parts. -/
theorem not_symplectic {p f : ℕ} (ho : Odd p) (hp : 2 ≤ p) (hf : 2 ≤ f)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hmodel : ClassicalGroup.IsPSp Q 2 (2^f)) :
    False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hc := (Nat.card_congr e.toEquiv).trans
    (Nat.card_congr (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm.toEquiv)
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, hF] at hc
  let q := 2^f
  have hq : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  have hc' : Nat.card Q = q^4*(q^4-1)*(q^2-1) := by rw [hc]; ring
  apply not_of_two_power_order_product (n := f*4) (b := q^2-1) ho hp hodd
  · rw [hc', pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · rw [pow_mul]; exact hc'.le
  · simpa only [pow_mul] using twice_square_lt_pow hq (by decide : 3 ≤ 4)

/-- The actual larger binary octonion groups have incompatible two-parts. -/
theorem not_g2 {p f : ℕ} (ho : Odd p) (hp : 2 ≤ p) (hf : 2 ≤ f)
    (hodd : ClassicalGroup.IsPSL Q 2 p) (hmodel : ClassificationModels.IsG2At Q (2^f)) :
    False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
  have hc := Nat.card_congr e.toEquiv
  rw [Atlas.G2.card_Model, hF] at hc
  let q := 2^f
  have hq : 4 ≤ q := by simpa [q] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hf
  apply not_of_two_power_order_product (n := f*6) (b := q^2-1) ho hp hodd
  · rw [hc, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · rw [pow_mul]; exact hc.le
  · simpa only [pow_mul] using twice_square_lt_pow hq (by decide : 3 ≤ 6)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels.LieParameter
