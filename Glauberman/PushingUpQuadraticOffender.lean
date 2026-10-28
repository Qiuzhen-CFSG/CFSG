module

public import Glauberman.QuadraticOffenderSelection
public import FeitThompson.BGsection6.Defs
public import Theory.GroupTheory.SylowCharacteristicKernelLifting
public import Theory.GroupTheory.PGroup.OmegaCenterIn

/-!
# The offender in the original pushing-up group

The absence of characteristic Sylow subgroups normal in the ambient group
forces the all-abelian Thompson subgroup outside the normal two-core.
The quadratic selection theorem then applies to the literal central omega
subgroup of that core, including its fixed central attachments.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 2.9, printed p.33,
up to assertion (4). The subsequent rank-one module recognition is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

theorem allAbelianThompson_top_characteristic :
    (thompsonSubgroup (⊤ : Subgroup G)).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro e
  exact thompsonSubgroup_top_map_mulEquiv e

theorem allAbelianThompson_subgroupOf_characteristic (S : Subgroup G) :
    ((thompsonSubgroup S).subgroupOf S).Characteristic := by
  have he : (thompsonSubgroup S).subgroupOf S =
      thompsonSubgroup (⊤ : Subgroup S) := by
    apply map_injective S.subtype_injective
    rw [map_subgroupOf_eq_of_le (thompsonSubgroup_le S),
      thompsonSubgroup_top_map_subtype]
  rw [he]
  exact allAbelianThompson_top_characteristic

theorem allAbelianThompson_ne_bot (S : Subgroup G) (hS : S ≠ ⊥) :
    thompsonSubgroup S ≠ ⊥ := by
  intro hJ
  obtain ⟨A,hA⟩ := thompsonAbelianSubgroups_nonempty S
  have hAeq : A = ⊥ := le_bot_iff.mp ((le_sSup hA).trans_eq hJ)
  apply hS
  apply le_bot_iff.mp
  intro x hx
  change x = 1
  have hcard := hA.2.2 (zpowers x) (zpowers_le.mpr hx) inferInstance
  rw [hAeq,card_bot] at hcard
  have hz : zpowers x = ⊥ := (zpowers x).eq_bot_of_card_le hcard
  have hmem : x ∈ zpowers x := mem_zpowers x
  simpa only [hz,mem_bot] using hmem

/-- This is the actual `J(S) ≰ Q` step in Niles 2.9; the all-abelian
Thompson subgroup is used in both groups. -/
theorem allAbelianThompson_not_le_normal (S Q : Subgroup G)
    [Q.Normal] (hQS : Q ≤ S) (hS : S ≠ ⊥)
    (hno : NoCharacteristicNormal S) : ¬ thompsonSubgroup S ≤ Q := by
  intro hJQ
  have hJS : thompsonSubgroup S ≤ S := thompsonSubgroup_le S
  have he : thompsonSubgroup Q = thompsonSubgroup S :=
    thompsonSubgroup_eq_of_le hQS hJQ
  let C := (thompsonSubgroup S).subgroupOf S
  have hC : C.Characteristic := allAbelianThompson_subgroupOf_characteristic S
  have hCJ : C.map S.subtype = thompsonSubgroup S := map_subgroupOf_eq_of_le hJS
  have hn : (C.map S.subtype).Normal := by
    rw [hCJ,←he,←thompsonSubgroup_top_map_subtype Q]
    let _ := allAbelianThompson_top_characteristic (G := Q)
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←normalizer_eq_top (H := Q)]
    exact normalizer_le_normalizer_characteristic_image Q _
  have hCb := hno C hC hn
  have hJb : thompsonSubgroup S = ⊥ := by
    rw [←hCJ,hCb,Subgroup.map_bot]
  exact allAbelianThompson_ne_bot S hS hJb

/-- A quadratic offender in the original group, with precisely the core
quotient index from Niles 2.9(4). No module recognition is assumed. -/
theorem pushingUp_quadratic_offender (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≠ ⊥)
    (hno : NoCharacteristicNormal (S : Subgroup G)) :
    ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups (S : Subgroup G) ∧
      ¬ A ≤ pCore 2 G ∧
      ⁅⁅omegaCenterIn (pCore 2 G), A⁆, A⁆ = ⊥ ∧
      (omegaCenterIn (pCore 2 G) ⊓ centralizer (A : Set G)).relIndex
        (omegaCenterIn (pCore 2 G)) ≤ (pCore 2 G).relIndex A := by
  let Q := pCore 2 G
  let V := omegaCenterIn Q
  have hQS : Q ≤ (S : Subgroup G) := pCore_isPGroup.le_sylow_of_normal S
  have hVQ : V ≤ Q := fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).1
  have hVc : IsMulCommutative V := inferInstance
  have hcentral : V ≤ centralizer (Q : Set G) :=
    fun _ hx => ((mem_omegaCenterIn_iff Q _).mp hx).2.1
  have hSV : (S : Subgroup G) ≤ normalizer (V : Set G) := by
    apply le_trans le_top
    rw [← normalizer_eq_top (H := Q)]
    exact normalizer_le_normalizer_omegaCenterIn Q
  obtain ⟨A,hA,hAQ,_,hquad⟩ := exists_quadratic_maximum_abelian_outside
    (S : Subgroup G) Q V S.isPGroup' (hVQ.trans hQS) hVc hSV hcentral
    (allAbelianThompson_not_le_normal _ Q hQS hS hno)
  exact ⟨A,hA,hAQ,hquad,maximum_abelian_offender_bound hA
    (hVQ.trans hQS) hVQ hVc hcentral⟩

end Glauberman
