module

public import Theory.GroupTheory.CentralizerSylowPromotion
public import Theory.GroupTheory.QuaternionCentralProductCenter

/-!
# Promoting a quaternion subgroup from a centralizer of order forty

A quaternion subgroup containing an involution z and centralizing z is
Sylow in its order-forty centralizer. Its center is precisely ⟨z⟩, so the
centralizer Sylow promotion theorem makes the same subgroup ambient Sylow.
The conclusion retains the literal subgroup, without conjugating it.

Source application: Aschbacher–Smith, J.2.7(5), printed p.435
(PDF p.446 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup
namespace Subgroup

theorem exists_sylow_of_quaternion_centralizer_card_forty {G : Type*} [Group G] [Finite G]
    (z : G) (hz : orderOf z = 2) (P : Subgroup G)
    (hPC : P ≤ centralizer ({z} : Set G)) (hzP : z ∈ P)
    (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hC : Nat.card (centralizer ({z} : Set G)) = 40) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
  have hPcard : Nat.card P = 8 := by
    obtain ⟨e⟩ := hP
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hZP : zpowers z ≤ P := zpowers_le.mpr hzP
  have hcomm : P ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure, centralizer_closure] using hPC
  have hcenter : (center P).map P.subtype = zpowers z := by
    have h := intersection_eq_factor_center P (zpowers z) hP
      (by rw [inf_eq_right.mpr hZP, Nat.card_zpowers, hz])
      (fun p hp a ha => (hcomm hp a ha).symm)
    simpa only [inf_eq_right.mpr hZP] using h.symm
  let S : Sylow 2 (centralizer ({z} : Set G)) :=
    Sylow.ofCard (P.subgroupOf (centralizer ({z} : Set G))) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv, hPcard, hC]
      decide +kernel)
  have hS : (S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype = P := map_subgroupOf_eq_of_le hPC
  obtain ⟨T,hT⟩ := exists_ambient_sylow_of_centralizer_center z hz S (by
    change (center ((S : Subgroup (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype)).map _ = _
    rw [hS]
    exact hcenter)
  exact ⟨T, hT.trans hS⟩

end Subgroup
