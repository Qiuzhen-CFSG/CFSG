module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalDoubledIntersection
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointOverlapExtension

/-!
# Extending the ordinary source amalgam across its common outside coset

An ordinary source-amalgam map on J=O²(H)V and L, together with a full plane
map agreeing on L, determines the doubled amalgam map. The original local
orders give [H:J]=2 and an element of the full overlap outside J. The plane
map restricts to the full overlap, while the two ordinary inclusion squares
give compatibility on its intersection with J. Point-overlap detection then
extends the point map across the outside coset, preserving that entire overlap.

All normality, index and outside-coset conditions come from the original source
hypotheses. The only inputs retained for final assembly are the ordinary
amalgam isomorphism and its compatible full plane map.

Source: Aschbacher--Smith 13.5.17, printed p.922, doubled normal A₅ branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.UnitaryTwo

private def upgradeOverlapRestriction {G K : Type*} [Group G] [Group K]
    {S B : Subgroup G} {S' B' : Subgroup K} (h : B ≤ S) (h' : B' ≤ S')
    (e : S ≃* S') (he : (B.subgroupOf S).map e.toMonoidHom = B'.subgroupOf S') : B ≃* B' :=
  (subgroupOfEquivOfLe h).symm.trans ((e.subgroupMap _).trans
    ((MulEquiv.subgroupCongr he).trans (subgroupOfEquivOfLe h')))

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hA312 hH hU hn

/-- Upgrade the original ordinary subamalgam and a compatible full plane
map to the literal doubled unitary amalgam, with both inclusion squares. -/
theorem source_normal_doubled_amalgam_of_compatible_maps
    (hdoubled : L ⊔ (T : Subgroup G) ≠ L)
    (e0 : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups ((pResidual 2 H).map H.subtype ⊔ V)
        ((residualCentralizer L V₁ ⊔ (T : Subgroup G)) ⊓ L) L
        ((normal_point_subgroup_overlap d hA312 hH hU hn).ge.trans inf_le_right)
        inf_le_right)
      (amalgam 1 (Nat.le_refl 1)))
    (eM : (L ⊔ (T : Subgroup G) : Subgroup G) ≃* Extension.plane 1 (Nat.le_refl 1))
    (hB : ((residualCentralizer L V₁ ⊔ (T : Subgroup G)).subgroupOf
        (L ⊔ (T : Subgroup G))).map eM.toMonoidHom =
      (Extension.overlap 1 (Nat.le_refl 1)).subgroupOf (Extension.plane 1 (Nat.le_refl 1)))
    (hM : ∀ l : L,
      (eM ⟨l, mem_sup_left l.property⟩ : Extension.ProjectiveExtension 1 (Nat.le_refl 1)) =
        SemidirectProduct.inl (e0.right l : ProjectiveGroup 1 (Nat.le_refl 1))) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups H (residualCentralizer L V₁ ⊔ (T : Subgroup G))
        (L ⊔ (T : Subgroup G)) hH.1.2
        (sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl))
      (Extension.amalgam 1 (Nat.le_refl 1))) := by
  let B := residualCentralizer L V₁ ⊔ (T : Subgroup G)
  let M := L ⊔ (T : Subgroup G)
  let C := B ⊓ L
  let J := (pResidual 2 H).map H.subtype ⊔ V
  let N := pResidual 2 H ⊔ V.subgroupOf H
  let D := B.subgroupOf H
  let P := pointParabolic 1 (Nat.le_refl 1)
  let EP := Extension.point 1 (Nat.le_refl 1)
  let EB := Extension.overlap 1 (Nat.le_refl 1)
  have hBH : B ≤ H := hH.1.2
  have hBM : B ≤ M := sup_le_sup ((map_subtype_le _).trans inf_le_left) le_rfl
  have hCJ : C ≤ J :=
    (normal_point_subgroup_overlap d hA312 hH hU hn).ge.trans inf_le_right
  have hVP : V ≤ H := d.chosen.le_sylow.trans (le_sup_right.trans hBH)
  have hmap : N.map H.subtype = J := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hVP]
  let j : N ≃* J := (N.equivMapOfInjective H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let eP : N ≃* P := j.trans e0.left
  have hEBr : EB ≤ Extension.plane 1 (Nat.le_refl 1) :=
    (Extension.exact_overlap 1 (Nat.le_refl 1)).ge.trans inf_le_right
  have hEBl : EB ≤ EP :=
    (Extension.exact_overlap 1 (Nat.le_refl 1)).ge.trans inf_le_left
  let eB0 : B ≃* EB := upgradeOverlapRestriction hBM hEBr eM hB
  let eB : D ≃* EB.subgroupOf EP :=
    (subgroupOfEquivOfLe hBH).trans (eB0.trans (subgroupOfEquivOfLe hEBl).symm)
  let : N.Normal := normal_point_split_subgroup_normal d hA312 hH hU hn
  obtain ⟨_, _, _, _, _, _, hcN⟩ := normal_point_split_subgroup d hA312 hH hU hn
  have hcards : Nat.card H = 1152 ∧ Nat.card B = 384 := by
    rcases normal_local_orders d hA312 hH hU hn with hc | hc
    · exact (hdoubled (eq_of_le_of_card_ge le_sup_left (by
        rw [hc.2.2, normal_local_card d hA312 hH hU hn])).symm).elim
    · exact ⟨hc.1, hc.2.1⟩
  have hindex : N.index = 2 := by
    have hc := N.card_mul_index
    rw [hcN, hcards.1] at hc
    omega
  have houtside : ∃ a : D, (a : H) ∉ N := by
    by_contra h
    push Not at h
    have hDN : D ≤ N := fun x hx => h ⟨x, hx⟩
    have hc := card_dvd_of_le hDN
    rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv, hcards.2, hcN] at hc
    norm_num at hc
  have hmark : ∀ n : N,
      eP n ∈ (overlap 1 (Nat.le_refl 1)).subgroupOf P → (n : H) ∈ D := by
    intro n hnB
    obtain ⟨c, hc⟩ := e0.middle.surjective
      (⟨(eP n : P).val, hnB⟩ : overlap 1 (Nat.le_refl 1))
    have he : (⟨c, hCJ c.property⟩ : J) = j n := e0.left.injective (by
      change e0.left ((RankTwoAmalgam.ofSubgroups J C L hCJ inf_le_right).left c) = eP n
      rw [e0.left_commutes c, hc]
      rfl)
    have hh := congrArg Subtype.val he
    change (c : G) = ((n : H) : G) at hh
    change ((n : H) : G) ∈ B
    rw [← hh]
    exact c.property.1
  have hcompat : ∀ (n : N) (hnD : (n : H) ∈ D),
      (PointOverlapExtension.ordinaryPointEquiv (eP n) : EP) =
        (eB ⟨n, hnD⟩ : EP) := by
    intro n hnD
    have hEq : B ⊓ J = C := normal_point_subgroup_overlap d hA312 hH hU hn
    have hnC : ((n : H) : G) ∈ C :=
      hEq ▸ (show ((n : H) : G) ∈ B ⊓ J from ⟨hnD, (j n).property⟩)
    let c : C := ⟨((n : H) : G), hnC⟩
    have hl : (e0.left (j n) : ProjectiveGroup 1 (Nat.le_refl 1)) =
        (e0.middle c : ProjectiveGroup 1 (Nat.le_refl 1)) :=
      congrArg Subtype.val (e0.left_commutes c)
    have hr : (e0.right ⟨((n : H) : G), hnC.2⟩ : ProjectiveGroup 1 (Nat.le_refl 1)) =
        (e0.middle c : ProjectiveGroup 1 (Nat.le_refl 1)) :=
      congrArg Subtype.val (e0.right_commutes c)
    apply Subtype.ext
    change SemidirectProduct.inl (e0.left (j n) : ProjectiveGroup 1 (Nat.le_refl 1)) =
      (eM ⟨((n : H) : G), hBM hnD⟩ : Extension.ProjectiveExtension 1 (Nat.le_refl 1))
    rw [hM ⟨((n : H) : G), hnC.2⟩]
    exact congrArg SemidirectProduct.inl (hl.trans hr.symm)
  obtain ⟨a, ha⟩ := houtside
  obtain ⟨eH, _, heB⟩ := PointOverlapExtension.exists_extension_to_graph_point
    N D hindex eP eB hmark hcompat a ha
  refine ⟨{
    left := eH
    middle := eB0
    right := eM
    left_commutes := ?_
    right_commutes := ?_ }⟩
  · intro b
    exact heB ⟨⟨b, hBH b.property⟩, b.property⟩
  · intro b
    rfl

end CFSG.Quasithin.Chapter13.Section05.A5Source
