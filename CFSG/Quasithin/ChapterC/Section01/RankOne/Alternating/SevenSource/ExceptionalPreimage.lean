module
public import Theory.SpecificGroups.Alternating.SevenFiveCover
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The actual exceptional five-letter preimage

The perfect A₅ lift in G/O₂(G) has no central kernel. Its inverse image has
only a two-group action kernel. The original O₂(G)Baum(T) maps onto the
chosen four-group and is exactly the lifted Sylow subgroup. B.2.3 therefore
identifies its Baumann subgroup with the unchanged original Baum(T).

Source: Aschbacher–Smith C.1.24(a), printed pp.130–131.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.SevenSource
open Theory.SpecificGroups.Alternating.SevenFiveCover
variable {G : Type*} [Group G] [Finite G]
local notation "A7" => alternatingGroup (Fin 7)

/-- Lift the marked A₅ and its four-group without discarding an odd cover. -/
theorem exceptional_five_preimage
    [Group.IsPerfect (G ⧸ pCore 2 G)]
    (q : G →* A7) (hQ : pCore 2 G ≤ q.ker)
    (hq : Function.Surjective q)
    (hc : (QuotientGroup.lift (pCore 2 G) q hQ).ker ≤ center (G ⧸ pCore 2 G))
    (T : Sylow 2 G) (A B : Subgroup A7)
    (hS : (ChapterB.baumann (T : Subgroup G)).map q = A)
    (hAB : A ≤ B) (e : B ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 B) (hP : (P : Subgroup B).map B.subtype = A) :
    ∃ H : Subgroup G, pCore 2 G ≤ H ∧ H.map q = B ∧
      IsPGroup 2 (q.ker.subgroupOf H) ∧
      ∃ P0 : Sylow 2 H,
        (ChapterB.baumann (P0 : Subgroup H)).map H.subtype =
          ChapterB.baumann (T : Subgroup G) := by
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  have hcomp : qb.comp π = q := by ext x; rfl
  have hqb : Function.Surjective qb := by
    intro a
    obtain ⟨g,rfl⟩ := hq a
    exact ⟨π g,rfl⟩
  let M := fiveLift qb B
  let H := M.comap π
  let S := ChapterB.baumann (T : Subgroup G)
  let R := pCore 2 G ⊔ S
  have hQR : pCore 2 G ≤ R := le_sup_left
  have hRT : R ≤ T := sup_le (pCore_isPGroup.le_sylow_of_normal T) inf_le_left
  have hpR : IsPGroup 2 R := T.isPGroup'.to_le hRT
  have hRq : R.map q = A := by
    rw [Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hQ,bot_sup_eq]
    exact hS
  have hRM : R.map π ≤ M := by
    apply two_subgroup_le_fiveLift qb hqb hc (pCore_quotient_pCore_eq_bot 2) B e _ (hpR.map π)
    rw [map_map,hcomp,hRq]
    exact hAB
  have hRH : R ≤ H := (map_le_iff_le_comap).mp hRM
  have hQH : pCore 2 G ≤ H := hQR.trans hRH
  have hHq : H.map q = B := by
    rw [←hcomp,←map_map]
    rw [show H.map π=M from map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) M]
    exact fiveLift_map qb hqb B e
  have hker : H ⊓ q.ker = pCore 2 G := by
    apply le_antisymm _ (le_inf hQH hQ)
    intro x hx
    have he : fiveLiftMap qb B ⟨π x,hx.1⟩ = 1 := by
      apply Subtype.ext
      exact hx.2
    have hi := fiveLiftMap_injective qb hqb hc (pCore_quotient_pCore_eq_bot 2) B e (he.trans (map_one _).symm)
    have hxπ : π x = 1 := congrArg Subtype.val hi
    exact (QuotientGroup.eq_one_iff x).mp hxπ
  have hk2 : IsPGroup 2 (q.ker.subgroupOf H) :=
    (pCore_isPGroup (p := 2) (G := G)).comap_subtype.to_le
      (show q.ker.subgroupOf H ≤ (pCore 2 G).subgroupOf H from
        fun x hx => hker.le ⟨x.property,hx⟩)
  let qH : H →* B := (q.comp H.subtype).codRestrict B (fun x => hHq ▸ mem_map_of_mem q x.property)
  have hqH : Function.Surjective qH := by
    intro b
    obtain ⟨x,hx,he⟩ := hHq.ge b.property
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  have hkH : IsPGroup 2 qH.ker := by
    have he : qH.ker = q.ker.subgroupOf H := by ext x; exact Subtype.ext_iff
    rw [he]
    exact hk2
  let P0 := P.comapOfKerIsPGroup qH hkH (by rw [MonoidHom.range_eq_top.mpr hqH]; exact le_top)
  have hP0 : (P0 : Subgroup H) = R.subgroupOf H := by
    ext x
    have hx : x ∈ (P0 : Subgroup H) ↔ q (x : G) ∈ A := by
      change qH x ∈ (P : Subgroup B) ↔ q (x : G) ∈ A
      rw [←hP]
      constructor
      · intro hx
        exact mem_map_of_mem B.subtype hx
      · rintro ⟨b,hb,he⟩
        exact (show b=qH x from Subtype.ext he) ▸ hb
    rw [hx]
    constructor
    · intro hxA
      obtain ⟨r,hr,he⟩ := hRq.ge hxA
      have hxR : (x : G) * r⁻¹ ∈ R := hQR (hker.le ⟨H.mul_mem x.property (H.inv_mem (hRH hr)),by
        change q ((x:G)*r⁻¹)=1
        rw [map_mul,map_inv,he,mul_inv_cancel]⟩)
      have hh := R.mul_mem hxR hr
      change (x : G) ∈ R
      simpa only [inv_mul_cancel_right] using hh
    · intro hxR
      exact hRq ▸ mem_map_of_mem q hxR
  refine ⟨H,hQH,hHq,hk2,P0,?_⟩
  have hb := Stellmacher.baumann_map_injective H.subtype H.subtype_injective (P0 : Subgroup H)
  change (ChapterB.baumann (P0 : Subgroup H)).map H.subtype =
    ChapterB.baumann ((P0 : Subgroup H).map H.subtype) at hb
  rw [hb,hP0,map_subgroupOf_eq_of_le hRH]
  exact (ChapterB.lemma_B_2_3_4 (T : Subgroup G) R le_sup_right hRT).symm
end CFSG.Quasithin.ChapterC.RankOne.SevenSource
