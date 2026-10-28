module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.RankOneModels.Orders
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
/-!
# The sporadic comparisons with the ordinary rank-one quotient

The already proved orders exclude all five Mathieu groups and Higman–Sims:
neither the order nor twice the order lies in the image of q ↦ q(q²−1).
The four remaining carrier comparisons are explicit prerequisites. This
reduction needs no additional sporadic order or simplicity certification.

Source: Aschbacher–Smith, 1.1.5(3)(f), printed pp.501–503, used in the
proof of 15.4.20, printed p.1164.
-/
@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
open ClassificationModels Sporadic.Mathieu

/-- Reduce the exact sporadic list to the four carriers for which a new
structural comparison is needed. This does not assume those comparisons. -/
theorem sporadic_separation_of_four
    (hfour : ∀ (name : SporadicName),
      (name = .j2 ∨ name = .j4 ∨ name = .he ∨ name = .ru) → ∀ {q : ℕ},
      ((∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q) →
      ¬ ClassicalGroup.IsPSL name.Carrier 2 q)
    (name : SporadicName) {q : ℕ} (hne : name ≠ .j3)
    (hq : (∃ n : ℕ, Even n ∧ q = 2^n) ∨ q.Prime ∧ Odd q)
    (hm : ClassicalGroup.IsPSL name.Carrier 2 q) : False := by
  cases name with
  | m11 =>
    exact psl_two_card_ne_of_gaps (c := 7920) (a := 19) (b := 25) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m11_order
  | m12 =>
    exact psl_two_card_ne_of_gaps (c := 95040) (a := 45) (b := 57) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m12_order
  | m22 =>
    exact psl_two_card_ne_of_gaps (c := 443520) (a := 76) (b := 96) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m22_order
  | m23 =>
    exact psl_two_card_ne_of_gaps (c := 10200960) (a := 216) (b := 273) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m23_order
  | m24 =>
    exact psl_two_card_ne_of_gaps (c := 244823040) (a := 625) (b := 788) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) m24_order
  | hs =>
    exact psl_two_card_ne_of_gaps (c := 44352000) (a := 353) (b := 445) hm
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier
  | j3 => exact hne rfl
  | j2 => exact hfour .j2 (Or.inl rfl) hq hm
  | j4 => exact hfour .j4 (Or.inr (Or.inl rfl)) hq hm
  | he => exact hfour .he (Or.inr (Or.inr (Or.inl rfl))) hq hm
  | ru => exact hfour .ru (Or.inr (Or.inr (Or.inr rfl))) hq hm
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.OrdinaryReduction.RankOneModels
