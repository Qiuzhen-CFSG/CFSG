module

public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourcePlacement
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# The literal ordinary-component normalizer modulo its center

C.2.12 identifies the normalizer of the source span with the original local
subgroup. Perfectness reflects that normalizer through the component's
central quotient. The local intersection has characteristic two, inherited
from the original local subgroup because the component is normal. Its
central quotient retains characteristic two as well.

The quotient map and both nested subgroup inclusions remain literal. The
unitary application is OriginalOddNormalizer.RudvalisNormalizer.
Source: Aschbacher--Smith C.2.12 and C.3.2--5, printed pp.148--150.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The full normalizer of the perfect span image is the image of the original
local intersection, and this image has self-centralizing two-core. -/
theorem ordinary_image_normalizer (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K) :
    let A := ((conjugateSpanBy L M).subgroupOf H).subgroupOf K
    let C := (M.subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    normalizer (A.map q : Set (K ⧸ center K)) = C.map q ∧
    centralizer (pCore 2 (C.map q) : Set (C.map q)) ≤ pCore 2 (C.map q) := by
  let X := conjugateSpanBy L M
  let A := (X.subgroupOf H).subgroupOf K
  let C := (M.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  have hXK := h.ordinary_span_le K hK
  let a : A ≃* X := (subgroupOfEquivOfLe hXK).trans (subgroupOfEquivOfLe hXH)
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  have hN : normalizer (A : Set K) = C := by
    rw [←subgroupOf_normalizer_eq hXK, ←subgroupOf_normalizer_eq hXH]
    ext x
    change (x : G) ∈ normalizer (X : Set G) ↔ (x : G) ∈ M
    constructor
    · intro hx
      exact h.normalizer_span_eq ▸ (show (x : G) ∈ H ⊓ normalizer (X : Set G) from
        ⟨x.val.property,hx⟩)
    · intro hx
      exact le_normalizer_conjugateSpanBy L M hx
  have hNC : normalizer (A.map q : Set (K ⧸ center K)) = C.map q := by
    have he := congrArg (map q) (comap_normalizer_map_eq_of_perfect q
      (by rw [QuotientGroup.ker_mk']) A)
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),hN] at he
    exact he
  refine ⟨hNC,?_⟩
  let M' := M.subgroupOf H
  let D := K.subgroupOf M'
  let := h.ordinary_component_normal K hK
  let : D.Normal := inferInstance
  let m : M' ≃* M := subgroupOfEquivOfLe h.local_le
  have hcM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    rw [←h.local_fitting]
    exact centralizer_generalizedFitting_le M
  have hcM' := (Theory.Quasithin.centralizer_pCore_le_iff 2 m).mpr hcM
  have hcD := normal_core_selfCentralizing hcM' D
  let d : D ≃* C := {
    toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hcC := (Theory.Quasithin.centralizer_pCore_le_iff 2 d).mp hcD
  let f := q.subgroupMap C
  apply f.centralizer_pCore_le_of_surjective_centralKernel (q.subgroupMap_surjective C) _ hcC
  intro x hx
  have hxZ : (x : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp
    (congrArg Subtype.val hx)
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hxZ y)
end CFSG.Quasithin.ChapterC.HypothesisC28
