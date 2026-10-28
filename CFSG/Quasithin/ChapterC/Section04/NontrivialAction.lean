module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ComponentEscape
public import Theory.GroupTheory.PerfectNormalizerCoreQuotient

/-!
# Nontrivial quotient action in the constrained escaping-component branch

The original span M0 is perfect and normalized by O2(H), since the latter
lies in R and hence in M. Its normalizer therefore pulls back exactly from
H/O2(H). Any subgroup escaping M must act nontrivially on that quotient
span; commutation symmetry gives the required nontrivial action of M0 on
the escaping component. The same conclusion holds modulo the component's
intrinsic two-core.

This supplies C.4.3 directly in the original group, without first replacing
H by K0 M0 TH. The radical-normalization and one-component quotient arguments
of C.4.4--7 remain separate.
Source: Aschbacher--Smith, quasithin C.4.3, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- Every subgroup escaping the original local M has nontrivial commutator
with M0 in the actual quotient H/O2(H). -/
theorem span_commutator_not_le_ambient_core
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hout : ¬ K ≤ M.subgroupOf H) :
    ¬ ⁅(conjugateSpanBy L M).subgroupOf H,K⁆ ≤ pCore 2 H := by
  let X := conjugateSpanBy L M
  have hXM : X ≤ M := conjugateSpanBy_le_self h.component_le
  have hXH : X ≤ H := hXM.trans h.local_le
  let A := X.subgroupOf H
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  have hQA : pCore 2 H ≤ normalizer (A : Set H) := by
    intro q hq x
    have hqM : (q : G) ∈ M := h.radical_le
      (h.ambient_core_le_radical (mem_map_of_mem H.subtype hq))
    exact le_normalizer_conjugateSpanBy L M hqM (x : G)
  intro hc
  have hn : K ≤ normalizer (A : Set H) :=
    normalizes_perfect_of_commutator_le A (pCore 2 H) K pCore_isPGroup hQA hc
  apply hout
  intro k hk
  have hnG : (k : G) ∈ normalizer (X : Set G) := by
    have hmap := A.le_normalizer_map H.subtype
    rw [map_subgroupOf_eq_of_le hXH] at hmap
    exact hmap (mem_map_of_mem H.subtype (hn hk))
  exact h.normalizer_span_eq ▸ (show (k : G) ∈ H ⊓ normalizer (X : Set G) from
    ⟨k.property,hnG⟩)

/-- The selected actual C-component has nontrivial action modulo its own
two-core, as required by C.4.3. -/
theorem span_commutator_not_le_component_core
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hout : ¬ K ≤ M.subgroupOf H) :
    ¬ ⁅(conjugateSpanBy L M).subgroupOf H,K⁆ ≤ K.pCoreIn 2 := by
  intro hc
  exact h.span_commutator_not_le_ambient_core K hout
    (hc.trans (pCoreIn_le_of_subnormal 2 hK.subnormal))

end CFSG.Quasithin.ChapterC.HypothesisC28
