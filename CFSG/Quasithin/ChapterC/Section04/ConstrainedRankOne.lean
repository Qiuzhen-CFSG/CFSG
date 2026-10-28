module
public import Theory.GroupTheory.PerfectMinimalSimpleTwoNormalizer
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedParabolic
public import Theory.GroupTheory.CoreCentralNormalizerAction.Normalizer
public import Theory.SpecificGroups.Alternating.FiveProperSubgroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
/-!
# The constrained A5 and rank-one Sylow obstructions

The radical has a nontrivial literal action on the component core quotient:
otherwise its normalizer control would contain the escaping component.
The perfect span normalizes that radical action. For an A5 central quotient,
minimal simplicity forces the span action to be the full inner group,
contradicting the trivial two-core of an automorphism overgroup.

Independently, a radical Sylow in KR is impossible because the perfect span
would preserve a Sylow subgroup and act trivially on the component quotient.
These arguments retain the original C.2.8 subgroups and allow outer radicals.

Source: Aschbacher–Smith C.4.4–6, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

theorem radical_commutator_not_le_component_core
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hout : ¬ K ≤ M.subgroupOf H) :
    ¬ ⁅K,R.subgroupOf H⁆ ≤ K.pCoreIn 2 := by
  have hcore : K.pCoreIn 2 ≤ R.subgroupOf H := by
    intro x hx
    exact h.ambient_core_le_radical
      (mem_map_of_mem H.subtype (pCoreIn_le_of_subnormal 2 hK.subnormal hx))
  intro hc
  have hn : K ≤ normalizer (R.subgroupOf H : Set H) :=
    le_normalizer_iff_commutator_le_right.mpr (hc.trans hcore)
  apply hout
  intro k hk
  have hng : (k : G) ∈ normalizer (R : Set G) := by
    have hm := (R.subgroupOf H).le_normalizer_map H.subtype
    rw [map_subgroupOf_eq_of_le (h.radical_le.trans h.local_le)] at hm
    exact hm (mem_map_of_mem H.subtype (hn hk))
  exact h.normalizer_le ⟨k.property,hng⟩

theorem constrained_radical_normalizes_intrinsic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    R.subgroupOf H ≤ normalizer (K : Set H) := by
  have hn := h.constrained_radical_normalizes K hK hq hout hfK
  intro r hr k
  change k ∈ K ↔ (r * k * r⁻¹ ∈ K)
  have hm (x : H) : x ∈ K ↔ (x : G) ∈ K.map H.subtype := by
    exact (mem_map_iff_mem H.subtype_injective).symm
  rw [hm,hm]
  exact hn hr (k : G)

theorem constrained_radical_action_nontrivial
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) :
    coreCentralActorImage K (R.subgroupOf H) ≠ ⊥ := by
  let := hq
  intro hb
  apply h.radical_commutator_not_le_component_core K hK hout
  rw [commutator_comm]
  exact commutator_le_core_of_coreCentralActorImage_eq_bot K _
    (h.constrained_radical_normalizes_intrinsic K hK hq hout hfK) hb

theorem no_constrained_component_of_minimal_simple_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hproper : ∀ B : Subgroup (coreCentralQuotient K), B ≠ ⊤ → Group.IsSolvable B) : False := by
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  let B := coreCentralActorImage K A
  let U := coreCentralActorImage K (R.subgroupOf H)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect B := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ha (r : G)
  have hU : IsPGroup 2 U := h.isRadical.isPGroup.comap_subtype.map _
  exact h.constrained_radical_action_nontrivial K hK hq hout hfK
    (MulAut.perfect_minimal_simple_normalizer_two_eq_bot hz hproper B U
      (h.constrained_span_action_nontrivial K hK hq hout) hU
      (coreCentralActorImage_normalizes K A (R.subgroupOf H) hAR))

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

theorem no_constrained_component_star_alternating_five
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin 5)) : False := by
  let ec := (coreCentralQuotientCongr
    (K.equivMapOfInjective H.subtype H.subtype_injective)).trans
      (Section04Constrained.source_simple_equiv
        (h.constrained_source_input K hK hq hout hfK) e
        (alternatingGroup.center_eq_bot (by simp)))
  exact h.no_constrained_component_of_minimal_simple_central_quotient K hK hq hout hfK
    (fun B hB => alternatingGroup.isSolvable_subgroup_of_equiv_five ec B hB)

theorem no_constrained_component_of_radical_sylow
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K)
    (hs : Chapter1.IsSylowIn 2 R (K.map H.subtype ⊔ R)) : False := by
  let Kg := K.map H.subtype
  have hKn : (Kg.subgroupOf (Kg ⊔ R)).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le Kg.le_normalizer (h.constrained_radical_normalizes K hK hq hout hfK))
  obtain ⟨T,hT⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hs le_sup_left hKn.isSubnormal
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let S : Sylow 2 K := T.mapSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hS : (S : Subgroup K).map K.subtype = R.subgroupOf H ⊓ K := by
    apply map_injective H.subtype_injective
    change (((T : Subgroup Kg).map eK.symm.toMonoidHom).map K.subtype).map H.subtype = _
    rw [map_map,map_map]
    have he : (H.subtype.comp K.subtype).comp eK.symm.toMonoidHom = Kg.subtype := by
      ext k
      exact congrArg (fun z : Kg => (z : G)) (eK.apply_symm_apply k)
    rw [he,hT]
    ext x
    constructor
    · rintro ⟨hxR,⟨k,hk,rfl⟩⟩
      exact ⟨k,⟨hxR,hk⟩,rfl⟩
    · rintro ⟨k,⟨hkR,hkK⟩,rfl⟩
      exact ⟨hkR,⟨k,hkK,rfl⟩⟩
  let := hq
  let X := conjugateSpanBy L M
  let A := X.subgroupOf H
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K)) :=
    ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable h.sqtk
      (.quotient_subgroup K (pCore 2 K))
  have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
    intro a ha r
    exact h.span_normalizes_radical ha (r : G)
  exact h.span_commutator_not_le_component_core K hK hout
    (commutator_le_core_of_perfect_sylow_preserving A K (R.subgroupOf H)
      (h.constrained_span_normalizes_intrinsic K hK hq) hAR S hS)

end CFSG.Quasithin.ChapterC.HypothesisC28
