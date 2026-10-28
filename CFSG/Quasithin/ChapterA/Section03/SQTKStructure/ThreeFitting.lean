module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem no_three_natural {B : Type*} [Group B] [Finite B]
    (h : A36Natural B) : ¬ 3 ∣ Nat.card (fittingSubgroup B) := by
  obtain ⟨he,p,hp,hgt,F,instF,finF,hF,v,e,hv⟩ := h
  let := instF
  let := finF
  have hc : Nat.card (generalizedFitting B) = p^2 := by
    rw [Nat.card_congr v.toEquiv]
    change Nat.card (Fin 2 → F) = p^2
    rw [Nat.card_fun,Nat.card_fin,hF]
  rw [←he,hc]
  intro hd
  rcases (Nat.dvd_prime hp).mp (Nat.prime_three.dvd_of_dvd_pow hd) with heq | heq <;> omega

private theorem central_fitting_quasisimple {B : Subgroup G} (hB : B.IsCComponent)
    (hf : fittingSubgroup B ≤ center B) : IsQuasisimple B := by
  have hr : solvableRadical B = center B := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hf)
    (le_solvableRadical (center B) inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm))
  let := hB.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩

theorem cComponent_quasisimple_of_fitting_three {κ : GroupClass.{u}}
    (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    (hF : IsPGroup 3 (fittingSubgroup G)) (B : Subgroup G) (hB : B.IsCComponent) :
    IsQuasisimple B := by
  apply central_fitting_quasisimple hB
  by_contra hn
  obtain ⟨alt,common⟩ := CComponentCommutation.noncentralStructureInput κ G hG hO B hB hn
  have hmap : IsPGroup 3 ((fittingSubgroup B).map B.subtype) :=
    hF.to_le (fittingSubgroup_map_subtype_le_of_isSubnormal B hB.subnormal)
  let e := (fittingSubgroup B).equivMapOfInjective B.subtype B.subtype_injective
  have hf : IsPGroup 3 (fittingSubgroup B) := hmap.of_injective e.toMonoidHom e.injective
  have h3 : 3 ∣ Nat.card (fittingSubgroup B) :=
    hf.card_eq_or_dvd.resolve_left (fun hc => hn ((Subgroup.card_eq_one.mp hc).le.trans bot_le))
  rcases alt with hnat | hnil
  · exact no_three_natural hnat h3
  · have hd : 3 ∣ Nat.card (generalizedFitting B) := by rw [hnil.1]; exact h3
    have hh := hnil.2.2.2 3 Nat.prime_three hd
    norm_num at hh
end CFSG.Quasithin.ChapterA.Section03
