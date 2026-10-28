module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAlternative
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedInput
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.QuasisimpleSections
public import Theory.GroupTheory.PerfectSylowPreservingAction
/-!
# C.4.4 for the original constrained escaping component

If R moves the component, the source alternative makes R intersect it in a
Sylow two-subgroup. The perfect span normalizes both groups, hence acts
trivially on the component's two-core quotient by the soluble Sylow
stabilizer theorem. This contradicts C.4.3. The known-simple outer input is
proved on the actual quasisimple section, so no model marking is assumed.

The final applications discharge the normalization premise in the literal
C.2.7 source input and obtain its proved kernel and offender conclusions.
Source: Aschbacher--Smith C.4.3--4, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

theorem constrained_radical_normalizes
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    R ≤ normalizer (K.map H.subtype : Set G) := by
  let := hq
  rcases h.constrained_component_sylow_or_normalized K hK hq hfK with ⟨T,hT⟩ | hn
  · let X := conjugateSpanBy L M
    have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
    let A := X.subgroupOf H
    let := h.span_perfect
    let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
      (subgroupOfEquivOfLe hXH).symm.surjective
    let : Group.IsSolvable (MulAut.Outer (K ⧸ pCore 2 K)) :=
      ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable h.sqtk
        (.quotient_subgroup K (pCore 2 K))
    have hAK : A ≤ normalizer (K : Set H) := by
      rcases Section04Constrained.component_orbit_bound h.sqtk hK with hn | hi
      · let := hn
        rw [normalizer_eq_top]
        exact le_top
      · exact le_of_isPerfect_of_index_le_two A _ hi.le
    have hAR : A ≤ normalizer (R.subgroupOf H : Set H) := by
      intro a ha y
      exact h.span_normalizes_radical ha (y : G)
    exact (h.span_commutator_not_le_component_core K hK hout
      (commutator_le_core_of_perfect_sylow_preserving A K (R.subgroupOf H) hAK hAR T hT)).elim
  · have hm := (map_mono (f := H.subtype) hn).trans (K.le_normalizer_map H.subtype)
    rwa [map_subgroupOf_eq_of_le (h.radical_le.trans h.local_le)] at hm

open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- All original C.2.7 input fields, including C.4.4, follow from C.2.8
and the selected constrained escaping component. -/
theorem constrained_source_input
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) :=
  h.constrained_input_of_radical_normalizes K hK hq hout hfK
    (h.constrained_radical_normalizes K hK hq hout hfK)

/-- The C.4 branch obtains C.2.7(1--2) on its original subgroups, without
an extra radical-normalization or ambient-normality premise. -/
theorem constrained_source_kernel_offender
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    KernelConclusion (K.map H.subtype) R ∧ OffenderConclusion (K.map H.subtype) R :=
  C27Source.kernel_offender_from_source (h.constrained_source_input K hK hq hout hfK)

end CFSG.Quasithin.ChapterC.HypothesisC28
