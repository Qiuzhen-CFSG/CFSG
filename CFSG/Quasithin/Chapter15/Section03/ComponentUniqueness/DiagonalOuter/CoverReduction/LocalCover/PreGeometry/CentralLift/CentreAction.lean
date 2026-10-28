module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.PreGeometry.Contracts
public import Theory.GroupTheory.PResidual.OddCoreSupplement

/-!
# The two-core has trivial action on the component centre

Image generation projects the actual Y₊ action to a cyclic outer image.
Since Y₊=Y is two-perfect, this cyclic image has odd order, so every two-group
maps trivially. Inner actions on the projective quotient lift to inner
actions on the perfect central cover and therefore fix its centre.

This uses the original quotientAction and marking throughout, without
assuming a product with y or that y centralizes Z(L).
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section

open Subgroup
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
open Candidates.LinearCore
variable {G : Type*} [Group G] [Finite G]

/-- Two-perfectness and cyclic outer image kill the outer action of every
two-subgroup of Y₊. No order or fixed-centre premise on y is needed. -/
theorem centralLift_twoSubgroup_inner {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}
    {n : ℕ} {c : ProjectiveMarking L (2^n)} {y : d.Yplus}
    (g : PreparedResiduals d I L c y) (H : Subgroup G)
    (hHY : H ≤ d.Yplus) (hH : IsPGroup 2 H) :
    (H.subgroupOf d.Yplus).map (quotientAction g.normalizes c.equivalence) ≤
      MulAut.innerSubgroup PSL(3,c.F) := by
  let ρ := quotientAction g.normalizes c.equivalence
  let π := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,c.F))
  let f := π.comp ρ
  have hi : ((componentPart d.Yplus L).subgroupOf d.Yplus).map ρ ≤
      MulAut.innerSubgroup PSL(3,c.F) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MatrixImage.quotientAction_on_component g.normalizes c.equivalence a
      ((map_subtype_le _ ha).2)]
    exact ⟨_, rfl⟩
  have hgen : f.range ≤ zpowers (f y) := by
    have hm := map_mono (f := π) g.image_generation
    have hbot : (((componentPart d.Yplus L).subgroupOf d.Yplus).map ρ).map π = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (by
        simpa only [π, QuotientGroup.ker_mk'] using hi)
    rw [Subgroup.map_sup, hbot, bot_sup_eq, MonoidHom.map_zpowers] at hm
    rw [MonoidHom.range_comp]
    exact hm
  let : IsCyclic f.range := isCyclic_of_injective (inclusion hgen) (inclusion_injective hgen)
  let : CommGroup f.range := IsCyclic.commGroup
  have hp : IsPPerfect 2 d.Yplus := g.plus.symm ▸ residualY_isPPerfect d.M d.Mc
  have ho := coprime_card_of_isPPerfect_commGroup
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  rintro _ ⟨a, ha, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  have hf : f.rangeRestrict a = 1 := by
    let a' : H := ⟨a, ha⟩
    have hd := orderOf_map_dvd (f.rangeRestrict.comp (inclusion hHY)) a'
    have hc := hH.orderOf_coprime ho a'
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc hd
      (orderOf_dvd_natCard (f.rangeRestrict a)))
  exact congrArg Subtype.val hf

omit [Finite G] in
/-- Innerness on the marked quotient forces the actor to fix Z(L);
this is an action statement, with no claim that the actor lies in L. -/
theorem centralLift_inner_centralizes_center {L : Subgroup G} {q : ℕ}
    (c : ProjectiveMarking L q) [Group.IsPerfect L]
    (hc : pCore 2 L ≤ center L) (a : normalizer (L : Set G))
    (ha : markedAction c a ∈ MulAut.innerSubgroup PSL(3,c.F)) :
    (a : G) ∈ centralizer (centerImage L : Set G) := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨u, rfl⟩ := c.equivalence.surjective v
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) u
  let l' := inclusion L.le_normalizer l
  have he : markedAction c a = markedAction c l' := by
    rw [markedAction_on_component]
    exact hv.symm
  have hk : (a : G) * (l : G)⁻¹ ∈ Chapter4.sectionCentralizer L :=
    (markedAction_eq_one_iff c (a * l'⁻¹)).mp (by
      rw [map_mul, map_inv, he, mul_inv_cancel])
  rw [sectionCentralizer_eq_centralizer_of_perfect hc] at hk
  have h₁ := centralizer_le (centerImage_le L) hk
  have h₂ := (le_centralizer_iff.mp (centerImage_centralizes L)) l.property
  have hm := (centralizer (centerImage L : Set G)).mul_mem h₁ h₂
  simpa only [inv_mul_cancel_right] using hm
end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
