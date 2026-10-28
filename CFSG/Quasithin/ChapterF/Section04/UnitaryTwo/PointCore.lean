module
public import Theory.GroupTheory.CenterTwoCoreSylowPromotion.NormalRadical
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFour.SylowGeometry
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.PointParabolic

/-!
# The center-two core of the unitary point parabolic

For the literal projective U4(2) flag model, the first parabolic has a
self-centralizing two-core whose center has order two. Its actual Heisenberg
radical is normal, self-centralizing and has center of order two; this already
forces the center of the full two-core, without an assumed radical identity.
The injective projective map transports both conclusions.

Source: Aschbacher--Smith F.4.29 and the U4(2) case of F.4.33,
printed pp.289--291. These are local model inputs, not recognition of a
completion.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointCore
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal

local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 (Nat.le_refl 1)
local notation "MP" => pointParabolicSU F (form F σ hσ)
local notation "Q" => UnitaryFourConverse.PointParabolic.parabolicRadical F σ hσ

theorem radical_center_card_two : Nat.card (center Q) = 2 := by
  let e : PointLocal.Radical 1 (Nat.le_refl 1) ≃* Q :=
    (PointLocal.Radical 1 (Nat.le_refl 1)).equivMapOfInjective
      (inclusion (localSU_le_pointParabolicSU F (standardForm 1 (Nat.le_refl 1))))
      (inclusion_injective _)
  exact (Nat.card_congr (centerCongr e.symm).toEquiv).trans
    (by simpa using PointLocal.radical_center_card 1 (Nat.le_refl 1))

theorem radical_selfCentralizing : centralizer (Q : Set ↥MP) ≤ Q := by
  intro x hx
  rw [← UnitaryFourConverse.PointParabolic.ambientRadical_subgroupOf]
  apply UnitaryFourConverse.PointParabolic.centralizer_ambientRadical_le F σ hσ
  intro r hr
  have hrP : (⟨r, UnitaryFourConverse.PointParabolic.ambientRadical_le_parabolic F σ hσ hr⟩ : ↥MP) ∈ Q := by
    rw [← UnitaryFourConverse.PointParabolic.ambientRadical_subgroupOf]
    exact hr
  exact congrArg Subtype.val (hx _ hrP)

theorem point_core_center_card : Nat.card (center (pCore 2 ↥MP)) = 2 :=
  center_twoCore_card_of_normal_selfCentralizing Q
    (UnitaryFourConverse.PointParabolic.parabolicRadical_isTwoGroup F σ hσ)
    radical_selfCentralizing radical_center_card_two


theorem projective_point_core_center_card :
    Nat.card (center (pCore 2 (pointParabolic 1 (Nat.le_refl 1)))) = 2 := by
  let e : ↥MP ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective
      (projection 1 (Nat.le_refl 1)) (projection_injective 1 (Nat.le_refl 1))
  let ec : pCore 2 ↥MP ≃* pCore 2 (pointParabolic 1 (Nat.le_refl 1)) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  exact (Nat.card_congr (centerCongr ec.symm).toEquiv).trans point_core_center_card

theorem projective_point_core_selfCentralizing :
    centralizer (pCore 2 (pointParabolic 1 (Nat.le_refl 1)) :
      Set (pointParabolic 1 (Nat.le_refl 1))) ≤ pCore 2 (pointParabolic 1 (Nat.le_refl 1)) := by
  let e : ↥MP ≃* pointParabolic 1 (Nat.le_refl 1) :=
    (pointParabolicMatrix 1 (Nat.le_refl 1)).equivMapOfInjective
      (projection 1 (Nat.le_refl 1)) (projection_injective 1 (Nat.le_refl 1))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
    (UnitaryFourConverse.PointParabolic.centralizer_twoCore_le F σ hσ)


/-- The marked central root subgroup in the projective point parabolic. -/
@[expose] def rootSubgroup : Subgroup (pointParabolic 1 (Nat.le_refl 1)) :=
  (center (pCore 2 (pointParabolic 1 (Nat.le_refl 1)))).map (pCore 2 _).subtype

theorem rootSubgroup_card : Nat.card rootSubgroup = 2 :=
  (card_map_of_injective (pCore 2 _).subtype_injective).trans projective_point_core_center_card

theorem rootSubgroup_central : rootSubgroup ≤ center (pointParabolic 1 (Nat.le_refl 1)) := by
  let : rootSubgroup.Normal := ConjAct.normal_of_characteristic_of_normal
  exact central_of_normal_card_two rootSubgroup rootSubgroup_card

end CFSG.Quasithin.ChapterF.UnitaryTwo.PointCore
