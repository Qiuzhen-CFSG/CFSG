module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup

namespace Stellmacher.SectionEight

open scoped commutatorElement IsMulCommutative

universe u

public theorem eight_six_index_two_centralizer_card
    {G : Type u} [Group G] [Finite G]
    (D V A Z : Subgroup G) [IsMulCommutative Z]
    (hAV : A ≤ V) (hindex : A.relIndex V ∣ 2)
    (hcentral : Z ≤ Subgroup.centralizer (D : Set G))
    (hcomm : ⁅D, V⁆ ≤ Z)
    (hfull : D ⊓ Subgroup.centralizer (V : Set G) = Z) :
    Nat.card (D ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤
      Nat.card Z * Nat.card Z := by
  let C := D ⊓ Subgroup.centralizer (A : Set G)
  obtain ⟨actor, hactor, hcosets⟩ :=
    Subgroup.relIndex_dvd_two_iff.mp hindex
  let actionCommutator : C →* Z := {
    toFun := fun member => ⟨⁅(member : G), actor⁆,
      hcomm (Subgroup.commutator_mem_commutator member.property.1 hactor)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro first second
      apply Subtype.ext
      change ⁅(first : G) * (second : G), actor⁆ =
        ⁅(first : G), actor⁆ * ⁅(second : G), actor⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hsecond := Subgroup.mem_centralizer_iff.mp
        (hcentral (hcomm
          (Subgroup.commutator_mem_commutator second.property.1 hactor)))
        first first.property.1
      rw [hsecond, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm
        (⟨⁅(second : G), actor⁆, hcomm
          (Subgroup.commutator_mem_commutator second.property.1 hactor)⟩ : Z)
        (⟨⁅(first : G), actor⁆, hcomm
          (Subgroup.commutator_mem_commutator first.property.1 hactor)⟩ : Z)) }
  have hkernel : actionCommutator.ker.map C.subtype = Z := by
    apply le_antisymm
    · rintro element ⟨member, hmember, rfl⟩
      rw [← hfull]
      refine ⟨member.property.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      have hfix : (member : G) * actor = actor * member :=
        commutatorElement_eq_one_iff_mul_comm.mp
          (congrArg Subtype.val (show actionCommutator member = 1 from hmember))
      intro other hother
      rcases hcosets other hother with hproduct | hin
      · apply mul_right_cancel (b := actor)
        calc
          other * (member : G) * actor = other * actor * member := by rw [mul_assoc, hfix, ← mul_assoc]
          _ = (member : G) * (other * actor) :=
            Subgroup.mem_centralizer_iff.mp member.property.2 _ hproduct
          _ = (member : G) * other * actor := (mul_assoc _ _ _).symm
      · exact Subgroup.mem_centralizer_iff.mp member.property.2 other hin
    · intro element helement
      have hfullmem := hfull.symm ▸ helement
      have hC : element ∈ C :=
        ⟨hfullmem.1, (Subgroup.centralizer_le hAV) hfullmem.2⟩
      refine Subgroup.mem_map.mpr ⟨⟨element, hC⟩, ?_, rfl⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hfullmem.2 actor hactor).symm)
  have hkerCard : Nat.card actionCommutator.ker = Nat.card Z := by
    exact (Nat.card_congr
      (actionCommutator.ker.equivMapOfInjective C.subtype C.subtype_injective).toEquiv).trans
        (congrArg (fun subgroup : Subgroup G => Nat.card subgroup) hkernel)
  calc
    Nat.card C = Nat.card actionCommutator.ker * actionCommutator.ker.index :=
      actionCommutator.ker.card_mul_index.symm
    _ = Nat.card Z * Nat.card actionCommutator.range := by rw [hkerCard, Subgroup.index_ker]
    _ ≤ Nat.card Z * Nat.card Z := Nat.mul_le_mul_left _
      actionCommutator.range.card_le_card_group

end Stellmacher.SectionEight
