module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.FittingOvergroup
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.NormalityReduction

/-!
# The contained-Fitting normality branch of C.4.8

Under the original C.2.8 hypotheses and M < H, containment of the preimage
of F*(H/O₂(H)) in M implies that M normalizes L. Otherwise the nonnormal
C-component promotion theorem places L in C(H), and the ambient-component
normality reduction gives a contradiction. The local conjugate span is
therefore L itself.

No normality, module identification, or quasisimple quotient is added to
the original assumptions. This proves the contained-Fitting branch needed
by C.4.8 directly; it does not assert all conclusions of C.2.13.
Source: Aschbacher--Smith C.2.13 and C.4.8, printed pp.148,153.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- The contained-Fitting branch gives the original C.4.8 normality conclusion. -/
theorem normalizes_of_fitting_contained
    (h : ChapterC.HypothesisC28 CFSG.KnownSimple.IsKnownSimple H M L R V)
    (hstrict : M < H)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  have hLH := h.component_le.trans h.local_le
  let A := L.subgroupOf H
  let N := M.subgroupOf H
  let e : N ≃* M := subgroupOfEquivOfLe h.local_le
  have he : (L.subgroupOf M).map e.symm.toMonoidHom = A.subgroupOf N := by
    ext x
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact hb
    · intro hx
      exact ⟨⟨(x : H),x.property⟩,hx,rfl⟩
  have hA : (A.subgroupOf N).IsCComponent := he ▸ h.component.map_equiv e.symm
  have hAN : A ≤ N := comap_mono h.component_le
  have hAn : ¬ (A.subgroupOf N).Normal := by
    intro hh
    have hnorm := (normal_subgroupOf_iff_le_normalizer hAN).mp hh
    have hm := (map_mono (f := H.subtype) hnorm).trans (A.le_normalizer_map H.subtype)
    rw [map_subgroupOf_eq_of_le hLH,map_subgroupOf_eq_of_le h.local_le] at hm
    exact hn hm
  have hQ : IsSQTK CFSG.KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (h.sqtk.stronglyQuasithin p hp ho)
  exact hn (h.normalizes_of_ambient_component hstrict (Chapter1.Section02.nonnormal_cComponent_of_twoCore_fitting_overgroup hAN hA hAn hQ hf))

/-- The original conjugate span collapses in the contained-Fitting branch. -/
theorem span_eq_of_fitting_contained
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V) (hstrict : M < H)
    (hf : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H) : conjugateSpanBy L M = L :=
  le_antisymm (conjugateSpanBy_le le_rfl (h.normalizes_of_fitting_contained hstrict hf))
    (le_conjugateSpanBy L M)

end CFSG.Quasithin.ChapterC.HypothesisC28
