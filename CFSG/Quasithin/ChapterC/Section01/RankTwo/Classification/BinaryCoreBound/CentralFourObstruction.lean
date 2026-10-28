module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Stellmacher.SectionsOneToFourDefs

/-!
# Central four-groups in a binary MS pair with Sylow radical

A central elementary four-group lies in the elementary center of the selected
Sylow two-subgroup. If that elementary center has order at most four, equality
makes its characteristic omega subgroup normal in the whole group, violating
MS3. This uses the literal selected radical and its Sylow identification.

The 15.3.24 consumer applies this to the actual natural-dual residual pair
and the original central-omega calculation of 15.3.8. It does not infer that
a subgroup central in a characteristic replacement is central in the original
group; that action transport remains explicit in the consumer.
Source: Aschbacher–Smith C.1.31(MS3), 15.3.8 and 15.3.24, pp. 135, 1123, 1129–1130.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}

/-- A central E4 contradicts MS3 when the selected radical is Sylow and
its elementary center has order at most four. -/
theorem Input.no_central_four_of_sylow (h : Input κ L R)
    (P : Sylow 2 J) (hR : R = (P : Subgroup J))
    (hbound : Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup J)) ≤ 4)
    (C : Subgroup J) [IsElementaryAbelian 2 C]
    (hcard : Nat.card C = 4) (hc : C ≤ center J) : False := by
  subst R
  let : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    simpa only [mem_center_iff.mp (hc hx) g,mul_inv_cancel_right] using hx
  have hCP : C ≤ (P : Subgroup J) :=
    (IsElementaryAbelian.isPGroup 2 C).le_sylow_of_normal P
  let O : Subgroup P := (omega₁ (center P) (p := 2)).map (center P).subtype
  have hCO : C ≤ O.map (P : Subgroup J).subtype := by
    intro c hcC
    have hz : (⟨c,hCP hcC⟩ : P) ∈ center P := by
      apply mem_center_iff.mpr
      intro s
      exact Subtype.ext (mem_center_iff.mp (hc hcC) s)
    refine ⟨⟨c,hCP hcC⟩,⟨⟨⟨c,hCP hcC⟩,hz⟩,subset_closure ?_,rfl⟩,rfl⟩
    change (⟨⟨c,hCP hcC⟩,hz⟩ : center P) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian c hcC (p := 2)
  have hEq : C = O.map (P : Subgroup J).subtype :=
    eq_of_le_of_card_ge hCO (hcard ▸ hbound)
  let : (omega₁ (center P) (p := 2)).Characteristic := omega₁_characteristic _
  have hOchar : O.Characteristic := by dsimp [O]; infer_instance
  have hOne : O ≠ ⊥ := by
    intro he
    rw [he,Subgroup.map_bot] at hEq
    simp [hEq] at hcard
  have hnormal : (O.map (P : Subgroup J).subtype).Normal := hEq ▸ inferInstance
  exact h.characteristic O hOchar hOne hnormal

end CFSG.Quasithin.ChapterC.BinaryMS
