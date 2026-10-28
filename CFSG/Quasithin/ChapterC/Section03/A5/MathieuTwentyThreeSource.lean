module
public import CFSG.Quasithin.ChapterC.Section03.A5.MathieuTwentyThree
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
public import Theory.Mathieu.SchurMultipliers.M23Kernel

/-!
# The literal C.2.8 consumer of the native M23 obstruction

All equivalences transport the original L and its characteristic U.
The C.2.8 normalizer bound and M-normality of L give the exact intrinsic
normalizer control in the containing ordinary component. The proved
trivial multiplier of M23 removes its possible central cover, after which
the native E16 obstruction applies. The component-containment premise is
precisely C.3.2; no C.3.1 classifier or local placement is assumed.
Source: Aschbacher–Smith C.3.1(4), C.3.2, printed pp.149–151, and 4.3.6,
printed pp.614–615.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

theorem no_normalized_alternatingFive_of_m23_equiv
    (e : G ≃* Sporadic.Mathieu.M23) (A : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hctrl : normalizer ((blockU A).map A.subtype : Set G) ≤ normalizer (A : Set G)) : False := by
  let B := A.map e.toMonoidHom
  let a : A ≃* B := e.subgroupMap A
  have hB : IsAlternatingBlock B 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a hA
  have hU : (blockU B).map B.subtype = ((blockU A).map A.subtype).map e.toMonoidHom := by
    rw [← RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  apply native_m23_no_normalized_alternatingFive B hB
  · rw [hU,←hc]
    exact (Nat.card_congr (e.subgroupMap ((blockU A).map A.subtype)).toEquiv).symm
  · rw [hU,← map_equiv_normalizer_eq]
    exact (map_mono hctrl).trans (map_equiv_normalizer_eq A e).le

namespace HypothesisC28
variable {κ : GroupClass} {H M L R V : Subgroup G}

theorem no_m23_subgroup_containing_block
    (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G))
    (hblock : IsAlternatingBlock L 5)
    (hU : (blockU L).map L.subtype = V) (hc : Nat.card V = 16)
    (K : Subgroup G) (hKH : K ≤ H) (hLK : L ≤ K)
    (e : K ≃* Sporadic.Mathieu.M23) : False := by
  let A := L.subgroupOf K
  let a : A ≃* L := subgroupOfEquivOfLe hLK
  have hA : IsAlternatingBlock A 5 := RankOne.Solvable.isAlternatingBlock_of_equiv a.symm hblock
  have hVK : V ≤ K := by rw [←hU]; exact (map_subtype_le _).trans hLK
  have hVA : (blockU A).map A.subtype = V.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hVK,←hU,←RankOne.Solvable.blockU_map_equiv a,map_map,map_map]
    rfl
  apply no_normalized_alternatingFive_of_m23_equiv e A hA
  · rw [hVA,Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv]
    exact hc
  · rw [hVA,←subgroupOf_normalizer_eq hVK,←subgroupOf_normalizer_eq hLK]
    intro x hx
    exact hnorm (h.module_normalizer ⟨hKH x.property,hx⟩)

theorem no_m23_ordinary_component
    (h : HypothesisC28 κ H M L R V)
    (hnorm : M ≤ normalizer (L : Set G))
    (hblock : IsAlternatingBlock L 5)
    (hU : (blockU L).map L.subtype = V) (hc : Nat.card V = 16)
    (K : Subgroup H) (hK : IsComponent H K) (hLK : L ≤ K.map H.subtype)
    (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M23) : False := by
  let := hK.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hf : Function.Bijective f :=
    ⟨(MonoidHom.ker_eq_bot_iff f).mp
        (Sporadic.Mathieu.SchurMultipliers.m23_centralQuotient_kernel_eq_bot e),
      e.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  let a := K.equivMapOfInjective H.subtype H.subtype_injective
  exact h.no_m23_subgroup_containing_block hnorm hblock hU hc (K.map H.subtype)
    (map_subtype_le _) hLK (a.symm.trans (MulEquiv.ofBijective f hf))
end HypothesisC28
end CFSG.Quasithin.ChapterC
