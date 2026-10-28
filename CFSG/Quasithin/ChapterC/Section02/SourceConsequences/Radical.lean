module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.OddCore
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.Subnormal
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PRadical
import Mathlib.Tactic
/-!
# The radical and full section centralizer under C.2.8

The source Sylow condition identifies R as the maximal signalizer of M0.
It follows that O2(M0R)=R and the original module lies in Z(R), proving
R nontrivial. Characteristic-normalizer control then gives radicality in H
and promotes the same literal R to a Sylow subgroup of the full section
centralizer. No Sylow subgroup is replaced by an abstract isomorphic copy.

Source: Aschbacher–Smith, C.2.9(2) and C.2.10(3), printed p.147.
-/
public section
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Subgroup Theory.GroupTheory ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem span_signalizer (h : HypothesisC28 κ H M L R V) :
    IsMaximalTwoSignalizer (conjugateSpanBy L M) M R := by
  let := h.span_perfect
  have hXM := conjugateSpanBy_le_self h.component_le
  have hn : ((conjugateSpanBy L M).subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXM).mpr (le_normalizer_conjugateSpanBy L M)
  exact (maximal_signalizer_iff_sylow _ _ _ hXM hn.isSubnormal perfect_twoPerfect).mpr
    h.section_sylow

/-- The actual R is the two-core of M0 R. -/
theorem span_join_core (h : HypothesisC28 κ H M L R V) :
    (conjugateSpanBy L M ⊔ R).pCoreIn 2 = R := by
  let X := conjugateSpanBy L M
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp h.span_signalizer
  have hRQ : R ≤ (X ⊔ R).pCoreIn 2 := le_pCoreIn_of_normalizes hm.1.isPGroup le_sup_right
    (sup_le hm.1.normalizes R.le_normalizer)
  refine le_antisymm (hm.2 _ ((isTwoSignalizer_iff _ _ _).mpr ?_) hRQ) hRQ
  exact ⟨(pCoreIn_le 2 _).trans (sup_le (conjugateSpanBy_le_self h.component_le) hm.1.le),
    isPGroup_pCoreIn 2 _, le_sup_left.trans ((X ⊔ R).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))⟩

/-- The actual module lies in the center of R, in particular R is nontrivial. -/
theorem module_le_center_radical (h : HypothesisC28 κ H M L R V) :
    V ≤ (center R).map R.subtype := by
  have hc := h.module_central
  rw [h.span_join_core] at hc
  exact hc

theorem radical_ne_bot (h : HypothesisC28 κ H M L R V) : R ≠ ⊥ := by
  intro he
  have hv := h.module_le_center_radical.trans (map_subtype_le _)
  exact h.module_nontrivial (bot_unique (he ▸ hv))

/-- The characteristic-normalizer condition controls the full relative normalizer. -/
theorem normalizer_le (h : HypothesisC28 κ H M L R V) :
    H ⊓ normalizer (R : Set G) ≤ M := by
  have hRH := h.radical_le.trans h.local_le
  have hn : R.subgroupOf H ≠ ⊥ := by
    intro he
    have hm := congrArg (map H.subtype) he
    exact h.radical_ne_bot (by simpa only [map_subgroupOf_eq_of_le hRH,Subgroup.map_bot] using hm)
  have hN := (normalizer_le_characteristicNormalizerClosure_self (R.subgroupOf H) hn).trans
    h.characteristic_control
  rw [← subgroupOf_normalizer_eq hRH] at hN
  intro x hx
  exact hN (show (⟨x,hx.1⟩ : H) ∈ (normalizer (R : Set G)).subgroupOf H from hx.2)

/-- C.2.9(2), first its literal actor-normalization assertion. -/
theorem span_normalizes_radical (h : HypothesisC28 κ H M L R V) :
    conjugateSpanBy L M ≤ normalizer (R : Set G) :=
  ((isMaximalTwoSignalizer_iff _ _ _).mp h.span_signalizer).1.normalizes

/-- C.2.9(2), with the original relative radical in H. -/
theorem isRadical (h : HypothesisC28 κ H M L R V) : IsPRadical 2 (R.subgroupOf H) := by
  let X := conjugateSpanBy L M
  let A := H ⊓ normalizer (R : Set G)
  have hRH := h.radical_le.trans h.local_le
  have hRA : R ≤ A := le_inf hRH R.le_normalizer
  have hRQ : R ≤ A.pCoreIn 2 := le_pCoreIn_of_normalizes h.radical_isTwoGroup hRA inf_le_right
  have hXA : X ≤ A := le_inf ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
    h.span_normalizes_radical
  have hm := (isMaximalTwoSignalizer_iff _ _ _).mp h.span_signalizer
  have he : A.pCoreIn 2 = R := by
    refine le_antisymm (hm.2 _ ((isTwoSignalizer_iff _ _ _).mpr ?_) hRQ) hRQ
    exact ⟨(pCoreIn_le 2 A).trans h.normalizer_le,isPGroup_pCoreIn 2 A,
      hXA.trans (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))⟩
  have hn : (normalizer (R.subgroupOf H : Set H)).map H.subtype = A := by
    rw [← subgroupOf_normalizer_eq hRH,subgroupOf_map_subtype,inf_comm]
  refine ⟨?_,?_⟩
  · intro hb
    apply h.radical_ne_bot
    have hm := congrArg (map H.subtype) hb
    simpa only [map_subgroupOf_eq_of_le hRH,Subgroup.map_bot] using hm
  · change (normalizer (R.subgroupOf H : Set H)).pCoreIn 2 = R.subgroupOf H
    apply map_injective H.subtype_injective
    rw [map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,hn,he,
      map_subgroupOf_eq_of_le hRH]

/-- C.2.10(3): the same R is Sylow in the full section centralizer in H. -/
theorem section_sylow_in_H (h : HypothesisC28 κ H M L R V) :
    ∃ S : Sylow 2 (twoSectionCentralizer (conjugateSpanBy L M) H),
      (S : Subgroup (twoSectionCentralizer (conjugateSpanBy L M) H)).map
        (twoSectionCentralizer (conjugateSpanBy L M) H).subtype = R := by
  apply exists_sylow_eq_of_relative_normalizer_le h.section_sylow
  · intro x hx
    exact ⟨h.local_le hx.1,hx.2⟩
  · intro x hx
    exact ⟨h.normalizer_le ⟨hx.1.1,hx.2⟩,hx.1.2⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
