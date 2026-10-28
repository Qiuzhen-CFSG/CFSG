module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
/-!
# Order bounds through a component's own central kernel

The kernel of the map from X ≤ L to its image in L/Z(L) embeds in Z(L).
Thus a center of order at most two increases the order of X by a factor
at most two, expressed here as divisibility. This makes no identification
between the centers of two components.

Application: Aschbacher–Smith 16.1.2(2) and the HS comparison in the proof
of 16.4.11(2), printed pp.1170 and 1193.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
variable {G : Type*} [Group G] [Finite G] {L X : Subgroup G}
omit [Finite G] in
theorem centralImageMap_kernel_card_dvd_center (hXL : X ≤ L) :
    Nat.card (centralImageMap hXL).ker ∣ Nat.card (center L) := by
  let f := centralImageMap hXL
  let j : f.ker →* center L :=
    ((inclusion hXL).comp f.ker.subtype).codRestrict (center L) (by
      intro x
      change (⟨x.val.val, hXL x.val.property⟩ : L) ∈ center L
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (center L) ⟨x.val.val, hXL x.val.property⟩ = 1
      have he := congrArg Subtype.val x.property
      simpa only [f, centralImageMap, MonoidHom.coe_mk, OneHom.coe_mk,
        Subgroup.coe_one] using he)
  apply card_dvd_of_injective j
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v : center L => (v.val.val : G)) he

theorem card_dvd_two_mul_centralImage (hXL : X ≤ L)
    (hZ : Nat.card (center L) ≤ 2) {n : ℕ}
    (himage : Nat.card (centralImage L X) ∣ n) : Nat.card X ∣ 2 * n := by
  have hk := centralImageMap_kernel_card_dvd_center hXL
  have hpos := Nat.card_pos (α := center L)
  have hz : Nat.card (center L) ∣ 2 := by
    have hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 2 := by omega
    rcases hc with hc | hc <;> simp [hc]
  let f := centralImageMap hXL
  have hc : Nat.card f.ker * Nat.card (centralImage L X) = Nat.card X := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (centralImageMap_surjective hXL)).toEquiv]
    exact f.ker.card_mul_index
  rw [← hc]
  exact Nat.mul_dvd_mul (hk.trans hz) himage
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
