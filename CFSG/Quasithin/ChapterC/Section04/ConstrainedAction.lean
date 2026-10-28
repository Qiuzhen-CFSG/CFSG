module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalization
public import Theory.GroupTheory.CoreCentralNormalizerAction.Kernel
/-!
# The actual perfect-span action on a component central quotient

The component orbit bound makes the perfect conjugate span normalize the
selected C-component. The known-simple section theorem proves soluble outer
automorphisms of its simple central quotient. Source C.4.3 makes the literal
normalizer-action image nontrivial, using faithfulness of central descent for
a perfect group. These statements retain the original C.2.8 subgroups.

Source: Aschbacher--Smith C.4.3--5, printed p.152.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

theorem constrained_core_central_outer_solvable
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    Group.IsSolvable (MulAut.Outer (coreCentralQuotient K)) := by
  let Q := K ⧸ pCore 2 K
  let S := Q ⧸ center Q
  let := hq
  let : IsSimpleGroup S := hq.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  have hna : ¬ IsMulCommutative S := Group.IsPerfect.not_isMulCommutative S
  have hc : center S = ⊥ := by
    rcases (inferInstance : (center S).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (hna (center_eq_top_iff.mp hc)).elim
  let : IsQuasisimple S := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hsec : ChapterA.Section02.IsSectionOf S H :=
    (ChapterA.Section02.IsSectionOf.of_surjective
      (QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)).trans
      ((ChapterA.Section02.IsSectionOf.of_surjective
        (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)).trans
        (.subgroup K))
  exact ChapterA.Section03.SourceComponents.quasisimple_section_outer_solvable h.sqtk hsec

theorem constrained_span_normalizes_intrinsic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K)) :
    (conjugateSpanBy L M).subgroupOf H ≤ normalizer (K : Set H) := by
  let := hq
  let X := conjugateSpanBy L M
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect (X.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  rcases Section04Constrained.component_orbit_bound h.sqtk hK with hn | hi
  · let := hn
    rw [normalizer_eq_top]
    exact le_top
  · exact le_of_isPerfect_of_index_le_two _ _ hi.le

theorem constrained_span_action_nontrivial
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥ := by
  let := hq
  intro hb
  exact h.span_commutator_not_le_component_core K hK hout
    (commutator_le_core_of_coreCentralActorImage_eq_bot K _
      (h.constrained_span_normalizes_intrinsic K hK hq) hb)

end CFSG.Quasithin.ChapterC.HypothesisC28
