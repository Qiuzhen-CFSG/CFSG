module

public import Stellmacher.SectionEight.GeneratedEightSixBaseSetup

namespace Stellmacher.SectionEight

open Later
open scoped commutatorElement IsMulCommutative

universe u

public theorem eight_six_relIndex_two_of_quotient_card
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hBA : B ≤ A) (hcard : QuotientCardEq A B 2) :
    B.relIndex A = 2 := by
  have hproduct := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv] at hproduct
  change Nat.card B * B.relIndex A = Nat.card A at hproduct
  have hpositive : 0 < Nat.card B := Nat.card_pos
  change Nat.card A = 2 * Nat.card B at hcard
  nlinarith

public theorem eight_six_abelian_index_two_centralizer_bound
    {G : Type u} [Group G] [Finite G]
    (D A Z : Subgroup G) [IsMulCommutative D] [IsMulCommutative Z]
    (hindex : (A ⊓ D).relIndex A ∣ 2)
    (hcentral : Z ≤ Subgroup.centralizer (D : Set G))
    (hcomm : ⁅D, A⁆ ≤ Z) :
    Nat.card D ≤ Nat.card (D ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
      Nat.card Z := by
  obtain ⟨actor, hactor, hcosets⟩ := Subgroup.relIndex_dvd_two_iff.mp hindex
  let actionCommutator : D →* Z := {
    toFun := fun member => ⟨⁅(member : G), actor⁆,
      hcomm (Subgroup.commutator_mem_commutator member.property hactor)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro first second
      apply Subtype.ext
      change ⁅(first : G) * (second : G), actor⁆ =
        ⁅(first : G), actor⁆ * ⁅(second : G), actor⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hsecond := Subgroup.mem_centralizer_iff.mp
        (hcentral (hcomm
          (Subgroup.commutator_mem_commutator second.property hactor)))
        first first.property
      rw [hsecond, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm
        (⟨⁅(second : G), actor⁆, hcomm
          (Subgroup.commutator_mem_commutator second.property hactor)⟩ : Z)
        (⟨⁅(first : G), actor⁆, hcomm
          (Subgroup.commutator_mem_commutator first.property hactor)⟩ : Z)) }
  have hkernel : actionCommutator.ker.map D.subtype =
      D ⊓ Subgroup.centralizer (A : Set G) := by
    apply le_antisymm
    · rintro element ⟨member, hmember, rfl⟩
      refine ⟨member.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      have hfix : (member : G) * actor = actor * member :=
        commutatorElement_eq_one_iff_mul_comm.mp
          (congrArg Subtype.val (show actionCommutator member = 1 from hmember))
      have hcommutes (other : G) (hother : other ∈ D) :
          other * (member : G) = (member : G) * other :=
        congrArg Subtype.val (mul_comm (⟨other, hother⟩ : D) member)
      intro other hother
      rcases hcosets other hother with hproduct | hin
      · apply mul_right_cancel (b := actor)
        calc
          other * (member : G) * actor = other * actor * member := by
            rw [mul_assoc, hfix, ← mul_assoc]
          _ = (member : G) * (other * actor) := hcommutes _ hproduct.2
          _ = (member : G) * other * actor := (mul_assoc _ _ _).symm
      · exact hcommutes other hin.2
    · intro element helement
      refine Subgroup.mem_map.mpr ⟨⟨element, helement.1⟩, ?_, rfl⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp helement.2 actor hactor).symm)
  have hkerCard : Nat.card actionCommutator.ker =
      Nat.card (D ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
    (Nat.card_congr
      (actionCommutator.ker.equivMapOfInjective D.subtype D.subtype_injective).toEquiv).trans
      (congrArg (fun subgroup : Subgroup G => Nat.card subgroup) hkernel)
  calc
    Nat.card D = Nat.card actionCommutator.ker * actionCommutator.ker.index :=
      actionCommutator.ker.card_mul_index.symm
    _ = Nat.card (D ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) *
        Nat.card actionCommutator.range := by rw [hkerCard, Subgroup.index_ker]
    _ ≤ _ := Nat.mul_le_mul_left _ actionCommutator.range.card_le_card_group

public theorem eight_six_quotient_card_one_or_two_of_bound
    {G : Type u} [Group G] [Finite G]
    (D Z : Subgroup G) (hZD : Z ≤ D) (hbound : Nat.card D ≤ 2 * Nat.card Z) :
    QuotientCardEq D Z 1 ∨ QuotientCardEq D Z 2 := by
  obtain ⟨index, hindex⟩ := Subgroup.card_dvd_of_le hZD
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hsmall : index ≤ 2 := by nlinarith
  have hnonzero : index ≠ 0 := by intro heq; simp [heq] at hindex; omega
  have hcases : index = 1 ∨ index = 2 := by omega
  rcases hcases with heq | heq
  · left
    change Nat.card D = 1 * Nat.card Z
    simpa [heq] using hindex
  · right
    change Nat.card D = 2 * Nat.card Z
    simpa [heq, Nat.mul_comm] using hindex

end Stellmacher.SectionEight
