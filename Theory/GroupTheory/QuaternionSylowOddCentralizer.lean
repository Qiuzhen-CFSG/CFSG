module
public import Theory.GroupTheory.QuaternionSylowPromotion
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.FullAutomizerNormalizerControl

/-!
# Quaternion Sylow promotion with odd local index

A quaternion subgroup containing an involution z has center exactly ⟨z⟩.
Its normalizer therefore fixes z. If its index in C(z) is odd, the
normalizer-index congruence makes it Sylow in the ambient group, with the
original inclusion retained.

This extends the order-forty specialization to the order-seventy-two
centralizers used by Fong–Wong, Nagoya Math. J.36 (1969), §3B(i), p.156.
The consumer is `G2Recognition.CubicCentralizer.cubic_quaternion_sylow`.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
theorem exists_sylow_of_quaternion_odd_centralizer_index
    (z : G) (hz : orderOf z = 2) (P : Subgroup G)
    (hPC : P ≤ centralizer ({z} : Set G)) (hzP : z ∈ P)
    (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hi : ¬ 2 ∣ P.relIndex (centralizer ({z} : Set G))) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P := by
  have hPcard : Nat.card P = 8 := by
    rw [Nat.card_congr hP.some.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have hZP : zpowers z ≤ P := zpowers_le.mpr hzP
  have hcomm : P ≤ centralizer (zpowers z : Set G) := by
    simpa only [zpowers_eq_closure,centralizer_closure] using hPC
  have hcenter : (center P).map P.subtype = zpowers z := by
    have hh := intersection_eq_factor_center P (zpowers z) hP
      (by rw [inf_eq_right.mpr hZP,Nat.card_zpowers,hz])
      (fun p hp a ha => (hcomm hp a ha).symm)
    simpa only [inf_eq_right.mpr hZP] using hh.symm
  exact exists_sylow_of_local_index P (centralizer ({z} : Set G))
    (IsPGroup.of_card (n := 3) hPcard) hi
    (normalizer_le_centralizer_of_characteristic_involution P (center P) z hz hcenter)
end Subgroup
