module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Contracts
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.PrimeCases
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Three
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.PowerFusion.Five

/-!
# HS power fusion with the order-eleven exception

The certified carrier order shows that the 512th power has odd order. The
independent three- and five-divisibility branches prove square fusion for those
odd orders, including mixed orders. Removing those primes leaves divisors of 77. The prime-case module
proves square fusion at seven, fourth-power fusion at eleven, and excludes 77
using the fixed points in the literal degree-100 action.

Thus `powerFusion` establishes the exact `PowerFusion` contract on the actual
HS carrier, discharging both inputs of `powerFusion_of_odd_branches` with their
proved producers. This module does not import the trace or degree assembly,
preserving its upstream boundary. The consumer's independent order-eleven
fixed-space premise remains with the representation calculation.

Source: ATLAS HSG1-p100B0 and the HS odd-order conjugacy classes,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/HS/. The precise consumer is
`degreeTwentyTraceField_of_powerFusion_of_elevenFixedFree` in `TraceField`.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField

open Sporadic.LeechRelated.HS

/-- Lagrange's theorem removes the entire two-part of the order. -/
theorem power_order_dvd_oddPart (g : KnownSimple.SporadicName.hs.Carrier) :
    orderOf (g ^ 512) ∣ 86625 := by
  apply orderOf_dvd_of_pow_eq_one
  rw [← pow_mul]
  change g ^ 44352000 = 1
  rw [← NormalizerIndex.card_carrier]
  exact pow_card_eq_one'

/-- The 512th power of every actual HS element has odd order. -/
theorem power_order_odd (g : KnownSimple.SporadicName.hs.Carrier) :
    Odd (orderOf (g ^ 512)) :=
  (by decide : Odd 86625).of_dvd_nat (power_order_dvd_oddPart g)

private theorem order_dvd_seventySeven (g : KnownSimple.SporadicName.hs.Carrier)
    (ho : Odd (orderOf g)) (h3 : ¬ 3 ∣ orderOf g) (h5 : ¬ 5 ∣ orderOf g) :
    orderOf g ∣ 77 := by
  have c2 : (orderOf g).Coprime (2 ^ 9) :=
    (Nat.coprime_two_right.mpr ho).pow_right _
  have c3 : (orderOf g).Coprime (3 ^ 2) :=
    (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).symm).pow_right _
  have c5 : (orderOf g).Coprime (5 ^ 3) :=
    (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm).pow_right _
  have hd : orderOf g ∣ 2 ^ 9 * (3 ^ 2 * (5 ^ 3 * 77)) := by
    change orderOf g ∣ 44352000
    rw [← NormalizerIndex.card_carrier]
    exact orderOf_dvd_natCard g
  exact c5.dvd_of_dvd_mul_left (c3.dvd_of_dvd_mul_left (c2.dvd_of_dvd_mul_left hd))

/-- Every odd-order element prime to fifteen is either trivial or has order
seven or eleven. The exclusion of 77 is proved on the actual permutation action. -/
theorem odd_order_cases_of_not_three_five (g : KnownSimple.SporadicName.hs.Carrier)
    (ho : Odd (orderOf g)) (h3 : ¬ 3 ∣ orderOf g) (h5 : ¬ 5 ∣ orderOf g) :
    orderOf g = 1 ∨ orderOf g = 7 ∨ orderOf g = 11 := by
  have hm := Nat.mem_divisors.mpr ⟨order_dvd_seventySeven g ho h3 h5, (by decide : 77 ≠ 0)⟩
  have hd : Nat.divisors 77 = {1, 7, 11, 77} := by decide
  rw [hd] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (TracePowerFusion.order_ne_seventySeven g h).elim

/-- The prime-case certificates and the two independent odd-order inputs give
fusion for every odd-order element, including mixed orders. -/
theorem oddPowerFusion_of_odd_branches
    (hthree : OddThreeSquareFusion) (hfive : OddFiveSquareFusion)
    (g : KnownSimple.SporadicName.hs.Carrier) (ho : Odd (orderOf g)) :
    IsConj g (g ^ 2) ∨ (orderOf g = 11 ∧ IsConj g (g ^ 4)) := by
  by_cases h3 : 3 ∣ orderOf g
  · exact Or.inl (hthree g ho h3)
  by_cases h5 : 5 ∣ orderOf g
  · exact Or.inl (hfive g ho h3 h5)
  rcases odd_order_cases_of_not_three_five g ho h3 h5 with h | h | h
  · have hg : g = 1 := orderOf_eq_one_iff.mp h
    exact Or.inl (by simp [hg])
  · exact Or.inl (TracePowerFusion.orderSeven_square_fusion g h)
  · exact Or.inr ⟨h, TracePowerFusion.orderEleven_fourthPower_fusion g h⟩

/-- Assembly for the exact trace-field consumer from the three- and
five-divisibility inputs. -/
theorem powerFusion_of_odd_branches
    (hthree : OddThreeSquareFusion) (hfive : OddFiveSquareFusion) : PowerFusion := by
  intro g
  simpa only [← pow_mul] using
    oddPowerFusion_of_odd_branches hthree hfive (g ^ 512) (power_order_odd g)

/-- Every HS element's 512th power is conjugate to its square, or has order
eleven and is conjugate to its fourth power. This discharges the group-fusion
premise of `degreeTwentyTraceField_of_powerFusion_of_elevenFixedFree`. -/
theorem powerFusion : PowerFusion :=
  powerFusion_of_odd_branches oddThreeSquareFusion oddFiveSquareFusion

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.TraceField
