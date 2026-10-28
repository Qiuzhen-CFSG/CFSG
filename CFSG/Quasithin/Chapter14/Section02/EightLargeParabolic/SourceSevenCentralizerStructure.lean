module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizer
public import Theory.GroupAction.ClassTwoCoprimeCentralizer
public import Theory.GroupTheory.PGroup.ExtraspecialCentralProduct

/-!
# The original order-seven fixed core is extraspecial

The original relative centralizer has order eight. Coprime class-two
centralization retains exactly the original central line, so this entire
fixed core is nonabelian and hence extraspecial. The actual ambient center
equality is retained; no choice between quaternion and dihedral type is made.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizerStructure
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The full order-seven centralizer in the original core is extraspecial
of order eight and has the same original ambient central line. -/
theorem source_seven_fixed_core_structure (A : Subgroup G) (hAH : A ≤ H)
    (hA : Nat.card A = 7) :
    let Q := H.pCoreIn 2
    let D := Q ⊓ centralizer (A : Set G)
    centerIn D = centerIn Q ∧ Nat.card D = 8 ∧ IsExtraspecial 2 D := by
  let Q := H.pCoreIn 2
  let D := Q ⊓ centralizer (A : Set G)
  obtain ⟨he,Z,hZ,hN,hel,ρ,d,hcoord,hi,hquot⟩ :=
    source_core_structure hG T hempty hM hu hmany hcard e H hH eR
  let _ := he
  have hQ : Nat.card Q = 512 :=
    (source_core_orders hG T hempty hM hu hmany hcard e H hH eR).1
  have hz2 : Nat.card (centerIn Q) = 2 := by
    rw [centerIn_eq_map_center,card_map_of_injective Q.subtype_injective]
    exact IsExtraspecial.center_order_p 2 Q
  have hAn : A ≤ normalizer (Q : Set G) := hAH.trans d.normalized
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  have hcenter : centerIn D = centerIn Q :=
    Theory.GroupAction.centerIn_centralizer_eq_of_class_two_coprime Q A hAn
      (inferInstance : Group.IsSolvable Q) (by rw [hA,hQ]; decide)
      (IsExtraspecial.quotient_elementary_abelian 2 Q).commutator_le_center_of_central_quotient
      (centerIn_centralizes_of_card_two hz2 hAn)
  have hD : Nat.card D = 8 :=
    SourceSevenCentralizer.source_seven_core_centralizer hG T hempty hM hu hmany hcard e H hH eR A hAH hA
  have hzD : Nat.card (center D) = 2 := by
    have hh := hcenter ▸ hz2
    rw [centerIn_eq_map_center,card_map_of_injective D.subtype_injective] at hh
    exact hh
  have hnon : ¬ IsMulCommutative D := by
    intro hm
    let _ := hm
    rw [center_eq_top,card_top,hD] at hzD
    contradiction
  exact ⟨hcenter,hD,IsExtraspecial.of_noncommutative_card_eight hD hnon⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceSevenCentralizerStructure
