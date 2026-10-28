module
public import Theory.GroupTheory.PResidual.SectionSylow

/-!
# Sylow subgroups in relative section centralizers

Let A be two-perfect, and let N contain A and a full ambient Sylow
subgroup T while normalizing A. Restricting to N makes A normal, so the
normal section-centralizer theorem identifies its Sylow subgroup with
O₂(AT). Transport through the literal subtype maps gives the same core
in the original ambient group. No normality of A in the whole group
is required.

The application is Y_z = C_{N_{C_G(z)}(X)}(X/O₂(X)) in the tensor case:
its original Sylow subgroup is S = O₂(XT).
Source: Aschbacher--Smith A.4.2(4) and 8.3.7, printed p.724.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- In a normalizing overgroup containing a full Sylow subgroup, the
centralizer of a two-perfect section has the expected original Sylow. -/
theorem exists_sylow_sectionCentralizer_of_normalizes
    (A N : Subgroup G) (hAN : A ≤ N) (hNA : N ≤ normalizer (A : Set G))
    (hA : IsPPerfect 2 A) (T : Sylow 2 G) (hTN : (T : Subgroup G) ≤ N) :
    ∃ P : Sylow 2 (commutatorPreimage N A (A.pCoreIn 2)),
      (P : Subgroup _).map (commutatorPreimage N A (A.pCoreIn 2)).subtype =
        (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let B := A.subgroupOf N
  let : B.Normal := normal_subgroupOf_of_le_normalizer hNA
  have hB : IsPPerfect 2 B := hA.of_surjective
    (subgroupOfEquivOfLe hAN).symm.toMonoidHom (subgroupOfEquivOfLe hAN).symm.surjective
  let S := T.subtype hTN
  let C := commutatorPreimage (⊤ : Subgroup N) B (B.pCoreIn 2)
  let Y := commutatorPreimage N A (A.pCoreIn 2)
  have hBm : B.map N.subtype = A := map_subgroupOf_eq_of_le hAN
  have hZm : (B.pCoreIn 2).map N.subtype = A.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup N.subtype
      (IsPGroup.ker_isPGroup_of_injective N.subtype_injective) B,hBm]
  let : (B.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 B).map B.subtype).Normal
  have hZnorm : N ≤ normalizer (A.pCoreIn 2 : Set G) :=
    hNA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  have hCm : C.map N.subtype = Y := by
    apply le_antisymm
    · apply le_commutatorPreimage (map_subtype_le _)
      conv_lhs => rw [←hBm,←map_commutator]
      rw [←hZm]
      exact map_mono (commutator_commutatorPreimage_le ⊤ B (B.pCoreIn 2)
        le_normalizer_of_normal)
    · have hYC : Y.subgroupOf N ≤ C := by
        apply le_commutatorPreimage le_top
        apply (map_le_map_iff_of_injective N.subtype_injective).mp
        rw [map_commutator,hBm,hZm,map_subgroupOf_eq_of_le
          (commutatorPreimage_le N A (A.pCoreIn 2))]
        exact commutator_commutatorPreimage_le N A (A.pCoreIn 2) hZnorm
      have hh := map_mono (f := N.subtype) hYC
      rwa [map_subgroupOf_eq_of_le (commutatorPreimage_le N A (A.pCoreIn 2))] at hh
  have hC : C = residualSectionCentralizer 2 B := by
    unfold residualSectionCentralizer
    rw [(pResidual_eq_top_iff 2 B).mpr hB,←MonoidHom.range_eq_map,range_subtype]
  let : C.Normal := hC.symm ▸ residualSectionCentralizer_normal B
  obtain ⟨R,hR⟩ := S.exists_sylow_map_eq_inf_of_normal C
  have hRcore : (R : Subgroup C).map C.subtype = (B ⊔ (S : Subgroup N)).pCoreIn 2 :=
    hR.trans (sylow_inf_sectionCentralizer_eq_join_core B hB S)
  let c : C ≃* Y := (C.equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr hCm)
  change ∃ P : Sylow 2 Y, (P : Subgroup Y).map Y.subtype = _
  refine ⟨R.mapSurjective (f := c.toMonoidHom) c.surjective,?_⟩
  change ((R : Subgroup C).map c.toMonoidHom).map Y.subtype = _
  rw [map_map]
  have he : Y.subtype.comp c.toMonoidHom = N.subtype.comp C.subtype := by ext; rfl
  rw [he,←map_map,hRcore,map_pCoreIn_of_ker_isPGroup N.subtype
    (IsPGroup.ker_isPGroup_of_injective N.subtype_injective),map_sup,hBm]
  change (A ⊔ ((T : Subgroup G).subgroupOf N).map N.subtype).pCoreIn 2 = _
  rw [map_subgroupOf_eq_of_le hTN]
end Subgroup
