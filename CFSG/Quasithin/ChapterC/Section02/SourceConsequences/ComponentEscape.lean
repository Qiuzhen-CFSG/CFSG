module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.FittingPreimage
public import Theory.GroupTheory.Fitting.OutsideComponent
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
/-!
# The actual component alternatives after C.2.11

The genuine C.2.8 data place the Fitting preimage inside the local subgroup.
If the generalized Fitting preimage escapes, an ordinary component in the
original two-core quotient lifts to an escaping C-component. Its core
quotient remains quasisimple. The actual perfect span of the original L
normalizes every component by the source orbit bound. Trivial odd core then
separates the ordinary and characteristic-two branches.

This supplies the component selection used at the start of C.3 and C.4.
The contained-preimage branch is retained explicitly; its index-two
conclusion is the separate C.2.13 obligation.
Source: Aschbacher–Smith C.2.11–13, C.3.1 and C.4.1, pp.148–151.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H M L R V : Subgroup G}

/-- An escaping ordinary quotient component lifts through the actual O₂(H). -/
theorem outside_component_of_generalizedFitting_escape
    (h : HypothesisC28 κ H M L R V)
    (hout : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H :=
  exists_cComponent_outside_of_fitting_preimage_le _ h.fitting_preimage_le hout

/-- The unconditional selection split, retaining the original quotient map. -/
theorem component_escape_or_generalizedFitting_le
    (h : HypothesisC28 κ H M L R V) :
    (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H := by
  by_cases hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H
  · exact .inl hf
  · exact .inr (h.outside_component_of_generalizedFitting_escape hf)

/-- The original perfect span fixes each member of the actual component family. -/
theorem component_normalized_by_span (h : HypothesisC28 κ H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) :
    conjugateSpanBy L M ≤ normalizer (K.map H.subtype : Set G) := by
  have hAH : conjugateSpanBy L M ≤ H :=
    (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let A := (conjugateSpanBy L M).subgroupOf H
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAH).symm.surjective
  have hQ : IsSQTK κ (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  have hn : A ≤ normalizer (K : Set H) := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hK with hN | hi
    · let := hN
      rw [normalizer_eq_top]
      exact le_top
    · exact le_of_isPerfect_of_index_le_two A _ hi.le
  intro x hx
  exact by
    have hxA : (⟨x,hAH hx⟩ : H) ∈ A := hx
    exact K.le_normalizer_map H.subtype (mem_map_of_mem H.subtype (hn hxA))

/-- The same selected component has precisely the two source structural alternatives. -/
theorem ordinary_or_constrained_escape
    (h : HypothesisC28 κ H M L R V)
    (hout : ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧
      conjugateSpanBy L M ≤ normalizer (K.map H.subtype : Set G) ∧
      (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  obtain ⟨K,hK,hq,ho⟩ := h.outside_component_of_generalizedFitting_escape hout
  exact ⟨K,hK,hq,ho,h.component_normalized_by_span K hK,
    hK.component_or_generalizedFitting_eq_pCore h.oddCore_eq_bot⟩

/-- Original C.2.8 consumer of the full Fitting-preimage calculation, with
no selected component, ordinary/constrained row or normalization premise. -/
theorem component_source_alternative (h : HypothesisC28 κ H M L R V) :
    (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H ∨
    ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K ≤ M.subgroupOf H ∧
      conjugateSpanBy L M ≤ normalizer (K.map H.subtype : Set G) ∧
      (IsComponent H K ∨ generalizedFitting K = pCore 2 K) := by
  by_cases hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H
  · exact .inl hf
  · exact .inr (h.ordinary_or_constrained_escape hf)
end CFSG.Quasithin.ChapterC.HypothesisC28
