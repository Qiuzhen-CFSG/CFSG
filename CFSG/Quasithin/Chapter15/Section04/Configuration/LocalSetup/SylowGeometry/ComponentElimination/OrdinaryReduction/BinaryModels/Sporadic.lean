module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Comparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.OrdinaryReduction.BinaryModels.Sporadic.J2Orbit
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M22.Properties.Order
public import Theory.Mathieu.M24.Properties.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismNormalizerIndex.CarrierOrder
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates

/-!
# Separating the sporadic alternatives from PSL₄(2) and PSL₅(2)

The existing Mathieu and Higman–Sims orders differ from the two binary
orders. In J₄, He, and Ru the checked elements of orders 37, 17, and 29
supply immediate obstructions. The J₂ case uses only a checked orbit
of length 100 in its actual permutation carrier. J₃ is excluded by the
literal 1.1.5(3)(f) alternative.

Every comparison concerns the fixed carrier in `SporadicName.Carrier`.
No unproved carrier comparison, general sporadic simplicity theorem, or
new full-order calculation is required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
1.1.5(3)(f), printed pp.501–503; proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
open ClassificationModels Sporadic.Mathieu

/-- Only the order obstructions needed for the ten sporadic alternatives
of 1.1.5(3)(f): no new sporadic simplicity or full-order result is needed. -/
theorem sporadic_separation (name : SporadicName) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hne : name ≠ .j3) (hm : ClassicalGroup.IsPSL name.Carrier n 2) : False := by
  have hb := binary_card hn hm
  cases name with
  | m11 =>
    change Nat.card M11 = _ at hb
    rw [m11_order] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | m12 =>
    change Nat.card M12 = _ at hb
    rw [m12_order] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | m22 =>
    change Nat.card M22 = _ at hb
    rw [m22_order] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | m23 =>
    change Nat.card M23 = _ at hb
    rw [m23_order] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | m24 =>
    change Nat.card M24 = _ at hb
    rw [m24_order] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | j2 => exact j2_separation hn hm
  | j3 => exact hne rfl
  | j4 =>
    have hd := orderOf_dvd_natCard (Janko4.a * Janko4.b)
    rw [Janko4.orderOf_a_mul_b] at hd
    change 37 ∣ Nat.card SporadicName.j4.Carrier at hd
    rw [hb] at hd
    rcases hn with rfl | rfl <;> norm_num at hd
  | hs =>
    change Nat.card Sporadic.LeechRelated.HS.Carrier = _ at hb
    rw [Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hb
    rcases hn with rfl | rfl <;> norm_num at hb
  | he =>
    have hd := orderOf_dvd_natCard (Held.a * Held.b)
    rw [Held.orderOf_ab] at hd
    change 17 ∣ Nat.card SporadicName.he.Carrier at hd
    rw [hb] at hd
    rcases hn with rfl | rfl <;> norm_num at hd
  | ru =>
    have hd := orderOf_dvd_natCard Rudvalis.w
    rw [Rudvalis.orderOf_w] at hd
    change 29 ∣ Nat.card SporadicName.ru.Carrier at hd
    rw [hb] at hd
    rcases hn with rfl | rfl <;> norm_num at hd

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.ComponentElimination.BinaryModels
