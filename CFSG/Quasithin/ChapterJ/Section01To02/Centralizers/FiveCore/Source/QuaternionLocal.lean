module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.Source.QuaternionLocal.Quotient
public import Theory.GroupTheory.QuaternionSylowPromotion
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Quotient calculations and Sylow promotion for the five-centralizer

The actual H → H/Q ≃ S₅ quotient map is injective on odd subgroups, since its
kernel is a two-group. Consequently their orders are one, three or five.
The cyclic centralizer of a five-cycle gives C_H(B₅) = B₅ C_Q(B₅).
Once the local quaternion isomorphism is supplied, this product has order
forty and center control promotes C_Q(B₅) to Sylow in C_G(B₅).

The last theorem is conditional: the Ru₂ fixed-section calculation and
quaternion recognition still have to construct its three local premises.
It does not assume a Sylow witness or the FiveQuaternionData record.

Source: Aschbacher–Smith, J.2.7(5), printed pp.435–436
(PDF pp.446–447 of `refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup

namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

include c in
/-- Complete the Sylow and order-forty fields once the local quaternion
calculation has supplied its isomorphism and position in the two sections. -/
theorem fiveQuaternionData_of_local_quaternion (hZ : Nat.card d.toTypeRuSetup.Z = 2)
    (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hq : Nonempty (CQ B5 ≃* QuaternionGroup 2))
    (hle : CQ B5 ≤ d.toTypeRuSetup.HC)
    (hinf : CQ B5 ⊓ d.toTypeRuSetup.U = d.toTypeRuSetup.Z) :
    Nonempty (FiveQuaternionData B5) := by
  have hCQ : Nat.card (CQ B5) = 8 := by
    obtain ⟨e⟩ := hq
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hc : Nat.card (d.toTypeRuSetup.H ⊓ G5 B5 : Subgroup G) = 40 := by
    rw [H_inf_G5_eq_B5Image_sup_CQ hZ B5,
      card_sup_eq_mul_of_normalizes_of_disjoint _ _
        (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
        (disjoint_of_coprime_natCard (by rw [B5Image_card hZ B5, hCQ]; decide)),
      B5Image_card hZ B5, hCQ]
  let z : G5 B5 := ⟨c.z, c.z_mem_G5 B5⟩
  let P := (CQ B5).subgroupOf (G5 B5)
  have hz : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf c.z = 2
    rw [← Nat.card_zpowers, ← c.z_generator, hZ]
  have hzP : z ∈ P :=
    ⟨d.ru2.six.kernel_le (d.ru2.natural.kernel_le c.z_mem_Z), c.z_mem_G5 B5⟩
  have hPC : P ≤ centralizer ({z} : Set (G5 B5)) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp
      (c.H_eq_centralizer_z ▸ ((pCoreIn_le 2 d.toTypeRuSetup.H) hx.1))
  have hP : Nonempty (P ≃* QuaternionGroup 2) := by
    obtain ⟨e⟩ := hq
    exact ⟨(subgroupOfEquivOfLe (show CQ B5 ≤ G5 B5 from inf_le_right)).trans e⟩
  have hmap : (centralizer ({z} : Set (G5 B5))).map (G5 B5).subtype =
      d.toTypeRuSetup.H ⊓ G5 B5 := by
    ext x
    rw [c.H_eq_centralizer_z]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy)), y.property⟩
    · intro hx
      exact ⟨⟨x,hx.2⟩, mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hx.1)), rfl⟩
  have hC : Nat.card (centralizer ({z} : Set (G5 B5))) = 40 := by
    rw [← card_map_of_injective (G5 B5).subtype_injective, hmap, hc]
  obtain ⟨S,hS⟩ := exists_sylow_of_quaternion_centralizer_card_forty z hz P hPC hzP hP hC
  exact ⟨{
    twoSylow := S
    twoSylow_image := by rw [hS]; exact map_subgroupOf_eq_of_le inf_le_right
    quaternion := hq
    local_product := H_inf_G5_eq_B5Image_sup_CQ hZ B5
    local_card := hc
    le_HC := hle
    inf_U := hinf
  }⟩
end CFSG.Quasithin.ChapterJ.Centralizers.Choices
