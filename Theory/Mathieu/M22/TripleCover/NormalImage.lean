module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.QuotientExtension.Matrix
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Normal perfect images in the triple-M₂₂ extension

A normal perfect subgroup with a seven-section lies in the normal
index-two triple cover. Quasisimplicity forces it to be the entire cover:
the alternative central image has order dividing three. Its literal
central quotient therefore maps onto M₂₂ with kernel of order three.

This is the normal point-image comparison for Aschbacher--Smith 12.9.4,
printed p.859, applied to G.11.2(13). The matrix carrier, scalar and
quotient identification are the imported ATLAS constructions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22TripleCover.NormalImage
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

/-- Such a normal perfect subgroup is the actual index-two triple cover. -/
theorem eq_cover (B : Subgroup actionGroup) [B.Normal] [Group.IsPerfect B]
    (h7 : 7 ∣ Nat.card B) : B = coverSubgroup := by
  have hBC : B ≤ coverSubgroup := le_of_isPerfect_of_index_eq_two B _ coverSubgroup_index
  let e : coverSubgroup ≃* M22TripleCover := subgroupOfEquivOfLe derivedGroup_le_actionGroup
  let : IsQuasisimple coverSubgroup := IsQuasisimple.of_mulEquiv e.symm
  rcases IsQuasisimple.normal_le_center_or_eq_top (B.subgroupOf coverSubgroup) with hz | ht
  · have hc : Nat.card (center coverSubgroup) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).trans M22TripleCover.center_card
    have hb : 7 ∣ Nat.card (B.subgroupOf coverSubgroup) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv]
    have hh := hb.trans (card_dvd_of_le hz)
    rw [hc] at hh
    exact ((by decide : ¬ 7 ∣ 3) hh).elim
  · exact le_antisymm hBC (subgroupOf_eq_top.mp ht)

/-- The resulting map to M₂₂ retains the order-three central kernel. -/
theorem exists_quotient (B : Subgroup actionGroup) [B.Normal] [Group.IsPerfect B]
    (h7 : 7 ∣ Nat.card B) :
    ∃ f : B →* M22, Function.Surjective f ∧ Nat.card f.ker = 3 := by
  let e := (MulEquiv.subgroupCongr (eq_cover B h7)).trans
    (subgroupOfEquivOfLe derivedGroup_le_actionGroup)
  let f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    ((QuotientGroup.mk' (center M22TripleCover)).comp e.toMonoidHom)
  have hf : Function.Surjective f := M22TripleCover.centralQuotientEquiv.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.surjective)
  refine ⟨f,hf,?_⟩
  have hh := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hf,card_top,Nat.card_congr e.toEquiv,
    M22TripleCover.card,m22_order] at hh
  omega
end Sporadic.Mathieu.M22TripleCover.NormalImage
