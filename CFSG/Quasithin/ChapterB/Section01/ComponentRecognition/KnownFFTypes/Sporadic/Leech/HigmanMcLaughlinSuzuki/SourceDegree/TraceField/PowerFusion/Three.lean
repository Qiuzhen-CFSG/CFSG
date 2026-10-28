module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three.CubicCoverage
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three.CentralizerBound

/-!
# Square fusion for odd three-divisible HS elements

The explicit Sylow nine-group proves one cubic class and excludes order nine.
Every element whose order is divisible by three centralizes a cubic power, so
a conjugate lies in the fixed cubic centralizer. A centralizer order dividing
360 then leaves just orders three and fifteen for the odd-order input.

For order fifteen, the cubic part is fixed first. Sylow conjugacy inside its
actual centralizer aligns the five-part with the checked fifteen-element.
The remaining cubic part is central there, giving a power of that element.
Its explicit square conjugator therefore proves the whole mixed-order branch.

The kernel-checked enumeration in `Three.CentralizerBound` proves that the
literal cubic centralizer has exactly 360 elements. Applying its divisibility
certificate discharges the final premise of `oddThreeSquareFusion`, which
supplies the three-divisibility input of `powerFusion_of_odd_branches`.
Source: ATLAS HSG1-p100B0, classes 3A and 15A,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/.
-/

public section
namespace Sporadic.LeechRelated.HS.ThreePowerFusion
open Subgroup

/-- Any element with three dividing its order has order dividing the cardinality
of the chosen cubic centralizer. -/
theorem order_dvd_cubicCentralizer_card (g : Carrier) (h3 : 3 ∣ orderOf g) :
    orderOf g ∣ Nat.card cubicCentralizer := by
  let n := orderOf g / 3
  have hp : orderOf (g ^ n) = 3 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h3
  obtain ⟨c, hc⟩ := isConj_iff.mp (cubic_class (g ^ n) hp).symm
  let d : cubicCentralizer := ⟨MulAut.conj c g, by
    apply mem_centralizer_singleton_iff.mpr
    have he : (MulAut.conj c g) ^ n = cubic := by
      rw [← map_pow]
      exact hc
    rw [← he]
    exact ((Commute.refl (MulAut.conj c g)).pow_right n).eq⟩
  have hd : orderOf d = orderOf g :=
    (orderOf_injective cubicCentralizer.subtype Subtype.val_injective d).symm.trans
      (MulEquiv.orderOf_eq (MulAut.conj c) g)
  rw [← hd]
  exact orderOf_dvd_natCard d

/-- The centralizer bound and the Sylow exponent leave exactly the two source
odd-order cases divisible by three. -/
theorem odd_order_cases_of_cubicCentralizer_card
    (hC : Nat.card cubicCentralizer ∣ 360)
    (g : Carrier) (ho : Odd (orderOf g)) (h3 : 3 ∣ orderOf g) :
    orderOf g = 3 ∨ orderOf g = 15 := by
  have hc : (orderOf g).Coprime (2 ^ 3) :=
    (Nat.coprime_two_right.mpr ho).pow_right _
  have hd360 := (order_dvd_cubicCentralizer_card g h3).trans hC
  have hd45 : orderOf g ∣ 45 := hc.dvd_of_dvd_mul_left hd360
  have hm := Nat.mem_divisors.mpr ⟨hd45, (by decide : 45 ≠ 0)⟩
  have hl : Nat.divisors 45 = {1, 3, 5, 9, 15, 45} := by decide
  rw [hl] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h | h | h
  · norm_num [h] at h3
  · exact Or.inl h
  · norm_num [h] at h3
  · exact (nine_not_dvd_order g (h ▸ dvd_rfl)).elim
  · exact Or.inr h
  · exact (nine_not_dvd_order g (h ▸ (by decide : 9 ∣ 45))).elim

private def fivePart : cubicCentralizer := ⟨fifteen ^ 6, by
  apply mem_centralizer_singleton_iff.mpr
  rw [← fifteen_fifth]
  exact ((Commute.refl fifteen).pow_pow 6 5).eq⟩

private theorem fivePart_order : orderOf fivePart = 5 := by
  rw [← orderOf_injective cubicCentralizer.subtype Subtype.val_injective fivePart]
  change orderOf (fifteen ^ 6) = 5
  rw [orderOf_pow' _ (by decide), fifteen_order]
  decide

private theorem fifteen_centralizer_fusion
    (hC : Nat.card cubicCentralizer ∣ 360)
    (d : Carrier) (hd : orderOf d = 15) (hd5 : d ^ 5 = cubic) : IsConj d (d ^ 2) := by
  let w : cubicCentralizer := ⟨d ^ 6, by
    apply mem_centralizer_singleton_iff.mpr
    rw [← hd5]
    exact ((Commute.refl d).pow_pow 6 5).eq⟩
  have hw : orderOf w = 5 := by
    rw [← orderOf_injective cubicCentralizer.subtype Subtype.val_injective w]
    change orderOf (d ^ 6) = 5
    rw [orderOf_pow' _ (by decide), hd]
    decide
  have hsq : ¬ 5 ^ 2 ∣ Nat.card cubicCentralizer := by
    intro h
    exact (by decide : ¬ 5 ^ 2 ∣ 360) (h.trans hC)
  obtain ⟨k, c, hc⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (G := cubicCentralizer) (by decide : Nat.Prime 5) hsq fivePart_order hw
  have hc6 : (MulAut.conj (c : Carrier)) ((fifteen ^ 6) ^ k) = d ^ 6 := by
    exact (congrArg Subtype.val hc).symm
  have hcx : (MulAut.conj (c : Carrier)) cubic = cubic := by
    change (c : Carrier) * cubic * (c : Carrier)⁻¹ = cubic
    rw [mem_centralizer_singleton_iff.mp c.property, mul_assoc, mul_inv_cancel, mul_one]
  have hd16 : d ^ 16 = d := by
    rw [← pow_mod_orderOf, hd]
    simp
  have he : (MulAut.conj (c : Carrier)) (fifteen ^ (10 + 6 * k)) = d := by
    calc
      (MulAut.conj (c : Carrier)) (fifteen ^ (10 + 6 * k)) =
          (MulAut.conj (c : Carrier)) ((fifteen ^ 5) ^ 2 * (fifteen ^ 6) ^ k) := by
            rw [← pow_mul, ← pow_mul, ← pow_add]
      _ = cubic ^ 2 * d ^ 6 := by rw [map_mul, map_pow, fifteen_fifth, hcx, hc6]
      _ = d ^ 16 := by rw [← hd5, ← pow_mul, ← pow_add]
      _ = d := hd16
  have hconj : IsConj (fifteen ^ (10 + 6 * k)) d := isConj_iff.mpr ⟨c, he⟩
  have hf : IsConj (fifteen ^ (10 + 6 * k)) ((fifteen ^ (10 + 6 * k)) ^ 2) := by
    simpa only [← pow_mul, Nat.mul_comm] using fifteen_square.pow (10 + 6 * k)
  exact (hconj.symm.trans hf).trans (hconj.pow 2)

/-- All order-fifteen carrier elements fuse with their squares once the fixed
cubic centralizer has the certified order bound. -/
theorem orderFifteen_square_of_cubicCentralizer_card
    (hC : Nat.card cubicCentralizer ∣ 360)
    (g : Carrier) (hg : orderOf g = 15) : IsConj g (g ^ 2) := by
  have hg5 : orderOf (g ^ 5) = 3 := by
    rw [orderOf_pow' _ (by decide), hg]
    decide
  obtain ⟨c, hc⟩ := isConj_iff.mp (cubic_class (g ^ 5) hg5).symm
  let d : Carrier := MulAut.conj c g
  have hd : orderOf d = 15 := (MulEquiv.orderOf_eq (MulAut.conj c) g).trans hg
  have hd5 : d ^ 5 = cubic := by
    change (MulAut.conj c g) ^ 5 = cubic
    rw [← map_pow]
    exact hc
  have hgd : IsConj g d := isConj_iff.mpr ⟨c, rfl⟩
  exact (hgd.trans (fifteen_centralizer_fusion hC d hd hd5)).trans (hgd.pow 2).symm

end Sporadic.LeechRelated.HS.ThreePowerFusion

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
open Sporadic.LeechRelated.HS.ThreePowerFusion

/-- Assembly of the complete odd-three fusion branch from the literal cubic
centralizer cardinal bound. -/
theorem oddThreeSquareFusion_of_cubicCentralizer_card
    (hC : Nat.card cubicCentralizer ∣ 360) : OddThreeSquareFusion := by
  intro g ho h3
  rcases odd_order_cases_of_cubicCentralizer_card hC g ho h3 with h | h
  · exact orderThree_square g h
  · exact orderFifteen_square_of_cubicCentralizer_card hC g h

/-- Every odd-order HS element whose order is divisible by three is conjugate
to its square, including every element of order fifteen. -/
theorem oddThreeSquareFusion : OddThreeSquareFusion :=
  oddThreeSquareFusion_of_cubicCentralizer_card cubicCentralizer_card_dvd

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
