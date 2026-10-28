module
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The original subgroup image in both component quotients

A C-component C of the local I has a canonical ambient copy C.map I.subtype.
The equivalence of their intrinsic two-core quotients and the equivalence
from C/O₂(C) to its image modulo O₂(I) both retain the original representatives.
Consequently every original subgroup of the ambient copy has the same image
under either induced model marking. Its subgroup inside the component image
maps back to its exact original star image.

Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
variable {G : Type*} [Group G] {Y : Type*} [Group Y]

/-- The supplied intrinsic marking on the canonical ambient copy of C. -/
@[expose] def ambientComponentEquiv (I : Subgroup G) (C : Subgroup I)
    (eC : (C ⧸ pCore 2 C) ≃* Y) :
    (C.map I.subtype ⧸ pCore 2 (C.map I.subtype)) ≃* Y :=
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans eC

/-- The ambient-copy marking retains every original component representative. -/
theorem ambientComponentEquiv_mk (I : Subgroup G) (C : Subgroup I)
    (eC : (C ⧸ pCore 2 C) ≃* Y) (c : C) :
    ambientComponentEquiv I C eC
      (QuotientGroup.mk' (pCore 2 (C.map I.subtype))
        (C.equivMapOfInjective I.subtype I.subtype_injective c)) =
      eC (QuotientGroup.mk' (pCore 2 C) c) := by
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  let Q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  change eC (Q.symm (QuotientGroup.mk' (pCore 2 (C.map I.subtype)) (e c))) = _
  rw [←QuotientGroup.congr_mk' (pCore 2 C) (pCore 2 (C.map I.subtype)) e
    (pCore_map_iso 2 e),Q.symm_apply_apply]

variable [Finite G]
/-- The supplied intrinsic marking on the actual component image in I/O₂(I). -/
@[expose] def componentImageEquiv (I : Subgroup G) (C : Subgroup I)
    (hC : C.IsCComponent) (eC : (C ⧸ pCore 2 C) ≃* Y) :
    C.map (QuotientGroup.mk' (pCore 2 I)) ≃* Y :=
  (cComponentTwoCoreQuotientEquiv hC).symm.trans eC

/-- The component-image marking retains every original representative. -/
theorem componentImageEquiv_mk (I : Subgroup G) (C : Subgroup I)
    (hC : C.IsCComponent) (eC : (C ⧸ pCore 2 C) ≃* Y) (c : C) :
    componentImageEquiv I C hC eC ((QuotientGroup.mk' (pCore 2 I)).subgroupMap C c) =
      eC (QuotientGroup.mk' (pCore 2 C) c) := by
  change eC ((cComponentTwoCoreQuotientEquiv hC).symm
    ((QuotientGroup.mk' (pCore 2 I)).subgroupMap C c)) = _
  exact congrArg eC ((cComponentTwoCoreQuotientEquiv hC).symm_apply_apply
    (QuotientGroup.mk' (pCore 2 C) c))

/-- The node subgroup has the same model image through the intrinsic ambient
component quotient and through its original image modulo O₂(I). -/
theorem ambient_component_subgroup_image
    (I : Subgroup G) (C : Subgroup I) (hC : C.IsCComponent)
    (eC : (C ⧸ pCore 2 C) ≃* Y) (P0 : Subgroup G) (hP0 : P0 ≤ C.map I.subtype) :
    (((P0.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).subgroupOf
      (C.map (QuotientGroup.mk' (pCore 2 I)))).map
        (componentImageEquiv I C hC eC).toMonoidHom =
    (P0.subgroupOf (C.map I.subtype)).map
      ((ambientComponentEquiv I C eC).toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (C.map I.subtype)))) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let e := C.equivMapOfInjective I.subtype I.subtype_injective
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨a,ha,he⟩ := hx
    obtain ⟨c,hc,hca⟩ := hP0 ha
    let c' : C := ⟨c,hc⟩
    have hxq : q.subgroupMap C c' = x := by
      apply Subtype.ext
      change q c = x.val
      rw [show c = a from Subtype.ext hca]
      exact he
    refine ⟨e c',?_,?_⟩
    · change (c : G) ∈ P0
      change (c : G) = (a : G) at hca
      rw [hca]
      exact ha
    · change ambientComponentEquiv I C eC
        (QuotientGroup.mk' (pCore 2 (C.map I.subtype)) (e c')) =
          componentImageEquiv I C hC eC x
      rw [ambientComponentEquiv_mk,←hxq,componentImageEquiv_mk]
  · rintro ⟨k,hk,rfl⟩
    obtain ⟨c,rfl⟩ := e.surjective k
    refine ⟨q.subgroupMap C c,?_,?_⟩
    · exact ⟨c.val,hk,rfl⟩
    · change componentImageEquiv I C hC eC (q.subgroupMap C c) =
        ambientComponentEquiv I C eC
          (QuotientGroup.mk' (pCore 2 (C.map I.subtype)) (e c))
      rw [componentImageEquiv_mk,ambientComponentEquiv_mk]

omit [Finite G] in
/-- Including the node subgroup of the component image recovers its exact
original image modulo O₂(I). -/
theorem component_subgroup_image_map_subtype
    (I : Subgroup G) (C : Subgroup I)
    (P0 : Subgroup G) (hP0 : P0 ≤ C.map I.subtype) :
    (((P0.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).subgroupOf
      (C.map (QuotientGroup.mk' (pCore 2 I)))).map
        (C.map (QuotientGroup.mk' (pCore 2 I))).subtype =
      (P0.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) := by
  apply map_subgroupOf_eq_of_le
  apply map_mono
  intro a ha
  obtain ⟨c,hc,he⟩ := hP0 ha
  exact (show c = a from Subtype.ext he) ▸ hc
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
