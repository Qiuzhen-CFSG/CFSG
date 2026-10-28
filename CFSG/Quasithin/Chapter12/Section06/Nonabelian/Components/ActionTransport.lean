module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Action
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Transporting the selected component action

The selected component in H/O₂(H) has trivial two-core, so its center
has odd order. The original X = KL₁V normalizes K, and every marked image
under its action agrees with the normalizer action of the literal image
in H/O₂(H). These identities allow centralizers to be transported without
identifying the original two-core kernel with the component center.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent
variable {G : Type*} [Group G] [Finite G] {E : Setup G} {H : Subgroup G}
  (c : E.SelectedComponent H)

/-- Subnormality puts the component two-core in the trivial ambient two-core. -/
theorem star_twoCore_eq_bot : pCore 2 (star H c.K) = ⊥ := by
  apply ((pCore 2 (star H c.K)).map_eq_bot_iff_of_injective (star H c.K).subtype_injective).mp
  apply bot_unique
  exact (pCoreIn_le_of_subnormal 2 c.component.1).trans_eq (pCore_quotient_pCore_eq_bot 2)

/-- The center of the actual selected star component has odd order. -/
theorem star_center_coprime_two : Nat.Coprime 2 (Nat.card (center (star H c.K))) :=
  (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)).mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot c.star_twoCore_eq_bot _ le_rfl)

namespace ActionMarking
variable {c} (a : c.ActionMarking)
omit [Finite G]

include a in
/-- The original action group normalizes the component after the star map. -/
theorem star_normalizes : star H c.localActor ≤ normalizer (star H c.K : Set (Hstar H)) := by
  let : (c.K.subgroupOf c.localActor).Normal := a.component_normal
  have hN : c.localActor ≤ normalizer (c.K : Set G) :=
    le_normalizer_of_normal_subgroupOf (le_sup_left.trans le_sup_left)
  exact (map_mono ((comap_mono hN).trans (c.K.le_normalizer_comap H.subtype))).trans
    ((c.K.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

/-- Every marked subgroup has the same image under the two literal actions. -/
theorem map_eq_star_normalizer_map (R : Subgroup G) (hR : R ≤ c.localActor) :
    (R.subgroupOf c.localActor).map a.action =
      ((star H R).subgroupOf (normalizer (star H c.K : Set (Hstar H)))).map
        (star H c.K).normalizerMonoidHom := by
  let B := star H c.K
  let N := normalizer (B : Set (Hstar H))
  let q := QuotientGroup.mk' (pCore 2 H)
  let j : c.localActor →* N := (q.comp (inclusion a.local_le)).codRestrict N
    (fun x => a.star_normalizes (mem_map_of_mem q x.property))
  have he : a.action = B.normalizerMonoidHom.comp j := by
    ext x k
    exact a.conjugation x k
  rw [he,←Subgroup.map_map]
  congr 1
  ext n
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact mem_map_of_mem q hx
  · rintro ⟨r,hr,he⟩
    exact ⟨⟨r.val,hR hr⟩,hr,Subtype.ext he⟩

/-- Identify the entire faithful range with the normalizer-action image. -/
theorem range_eq_star_normalizer_map : a.action.range =
    ((star H c.localActor).subgroupOf (normalizer (star H c.K : Set (Hstar H)))).map
      (star H c.K).normalizerMonoidHom := by
  rw [←a.map_eq_star_normalizer_map c.localActor le_rfl,subgroupOf_self,MonoidHom.range_eq_map]

/-- Restricting the codomain retains each literal marked image. -/
theorem map_rangeRestrict (R : Subgroup G) :
    (R.subgroupOf c.localActor).map a.action.rangeRestrict =
      ((R.subgroupOf c.localActor).map a.action).subgroupOf a.action.range := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact mem_map_of_mem a.action hx
  · rintro ⟨x,hx,he⟩
    exact ⟨x,hx,Subtype.ext he⟩

end ActionMarking
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent
