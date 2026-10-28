module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearThree.MarkedAutomizer.ModelDefs
public import Theory.GroupTheory.PCoreSurjective

/-!
# Transport to the literal cover parabolic section

Restrict the genuine quotient map L → L/O₂(L) ≃ Â₆ to R ≤ L. When its
image is the model residual, this gives a surjection with two-group kernel.
The preimage theorem for two-cores therefore identifies R/O₂(R) with the
model residual's own two-core quotient. The comparison intertwines actual
ambient conjugation, and proves that each element of N_M(R) preserves the
model residual. No equality of independently chosen actions is assumed.

This is a transport for Aschbacher–Smith 13.8.16(1), printed p.952
(PDF p.969). The image identification is a separate geometric obligation;
this module does not assume or compute the final E₄ automizer.
-/

@[expose] public section

open Subgroup Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer
variable {G : Type*} [Group G] {L V : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}

namespace CoverPointModel
noncomputable def subgroupMap (d : CoverPointModel L V hLV) (R : Subgroup G) (hRL : R ≤ L) :
    R →* Model.Cover :=
  d.quotientEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hRL))

theorem subgroupMap_ker (d : CoverPointModel L V hLV) (R : Subgroup G) (hRL : R ≤ L) :
    (d.subgroupMap R hRL).ker = (pCore 2 L).comap (inclusion hRL) := by
  ext r
  change d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hRL r)) = 1 ↔ _
  rw [d.quotientEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff _

noncomputable def toModelResidual (d : CoverPointModel L V hLV)
    (R : Subgroup G) (hRL : R ≤ L) (x : BinaryPoint)
    (hr : (d.subgroupMap R hRL).range = Model.residual x) : R →* Model.residual x :=
  (d.subgroupMap R hRL).codRestrict _ (fun r => show d.subgroupMap R hRL r ∈ Model.residual x from hr ▸ ⟨r, rfl⟩)

theorem toModelResidual_surjective (d : CoverPointModel L V hLV)
    (R : Subgroup G) (hRL : R ≤ L) (x : BinaryPoint)
    (hr : (d.subgroupMap R hRL).range = Model.residual x) :
    Function.Surjective (d.toModelResidual R hRL x hr) := by
  intro r
  have hm : (r : Model.Cover) ∈ (d.subgroupMap R hRL).range := by
    rw [hr]
    exact r.property
  obtain ⟨s, hs⟩ := hm
  exact ⟨s, Subtype.ext hs⟩

noncomputable def sectionEquiv [Finite G] (d : CoverPointModel L V hLV)
    (R : Subgroup G) (hRL : R ≤ L) (x : BinaryPoint)
    (hr : (d.subgroupMap R hRL).range = Model.residual x) :
    (R ⧸ pCore 2 R) ≃* Model.Section x := by
  let f := d.toModelResidual R hRL x hr
  have hf := d.toModelResidual_surjective R hRL x hr
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((d.subgroupMap R hRL).codRestrict _ _).ker
    rw [MonoidHom.ker_codRestrict, d.subgroupMap_ker]
    exact pCore_isPGroup.comap_of_injective (inclusion hRL) (inclusion_injective hRL)
  let g := (QuotientGroup.mk' (pCore 2 (Model.residual x))).comp f
  have hker : g.ker = pCore 2 R := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g ((QuotientGroup.mk'_surjective _).comp hf))

theorem sectionEquiv_mk [Finite G] (d : CoverPointModel L V hLV)
    (R : Subgroup G) (hRL : R ≤ L) (x : BinaryPoint)
    (hr : (d.subgroupMap R hRL).range = Model.residual x) (r : R) :
    d.sectionEquiv R hRL x hr (QuotientGroup.mk' (pCore 2 R) r) =
      QuotientGroup.mk' (pCore 2 (Model.residual x)) (d.toModelResidual R hRL x hr r) := rfl

/-- The quotient action on L intertwines the actual conjugation on R. -/
theorem subgroupMap_conjugation (d : CoverPointModel L V hLV)
    (R M : Subgroup G) (hRL : R ≤ L) (hML : M ≤ normalizer (L : Set G))
    (m : (M ⊓ normalizer (R : Set G) : Subgroup G)) (r : R) :
    d.subgroupMap R hRL (R.normalizerMonoidHom (inclusion inf_le_right m) r) =
      coverAction d M hML (inclusion inf_le_left m) (d.subgroupMap R hRL r) := by
  change d.quotientEquiv (QuotientGroup.mk' (pCore 2 L) _) =
    d.quotientEquiv (quotientAction L M hML (inclusion inf_le_left m)
      (d.quotientEquiv.symm (d.quotientEquiv _)))
  rw [MulEquiv.symm_apply_apply, MonoidHom.comp_apply, quotientAction_mk]
  rfl

/-- Every actual actor preserves the model residual image. -/
theorem coverAction_preserves_residual (d : CoverPointModel L V hLV)
    (R M : Subgroup G) (hRL : R ≤ L) (hML : M ≤ normalizer (L : Set G))
    (x : BinaryPoint) (hr : (d.subgroupMap R hRL).range = Model.residual x)
    (m : (M ⊓ normalizer (R : Set G) : Subgroup G)) :
    (Model.residual x).map
      (coverAction d M hML (inclusion inf_le_left m)).toMonoidHom = Model.residual x := by
  have he : (coverAction d M hML (inclusion inf_le_left m)).toMonoidHom.comp
      (d.subgroupMap R hRL) = (d.subgroupMap R hRL).comp
        (R.normalizerMonoidHom (inclusion inf_le_right m)).toMonoidHom := by
    apply MonoidHom.ext
    intro r
    exact (d.subgroupMap_conjugation R M hRL hML m r).symm
  rw [← hr, ← MonoidHom.range_comp, he, MonoidHom.range_comp,
    (show (R.normalizerMonoidHom (inclusion inf_le_right m)).toMonoidHom.range = ⊤ from
      MonoidHom.range_eq_top.mpr (R.normalizerMonoidHom (inclusion inf_le_right m)).surjective),
    ← MonoidHom.range_eq_map]

/-- This is compatibility for the literal source automizer, whose domain is N_M(R). -/
theorem sectionEquiv_intertwines [Finite G] (d : CoverPointModel L V hLV)
    (R M : Subgroup G) (hRL : R ≤ L) (hML : M ≤ normalizer (L : Set G))
    (x : BinaryPoint) (hr : (d.subgroupMap R hRL).range = Model.residual x)
    (m : (M ⊓ normalizer (R : Set G) : Subgroup G)) (r : R ⧸ pCore 2 R) :
    d.sectionEquiv R hRL x hr (automizerAction R M m r) =
      Model.sectionAut x (coverAction d M hML (inclusion inf_le_left m))
        (d.coverAction_preserves_residual R M hRL hML x hr m)
        (d.sectionEquiv R hRL x hr r) := by
  induction r using Quotient.inductionOn with
  | h r =>
    change d.sectionEquiv R hRL x hr
      (quotientAction R (M ⊓ normalizer (R : Set G)) inf_le_right m
        (QuotientGroup.mk' (pCore 2 R) r)) =
      Model.sectionAut x (coverAction d M hML (inclusion inf_le_left m))
        (d.coverAction_preserves_residual R M hRL hML x hr m)
        (d.sectionEquiv R hRL x hr (QuotientGroup.mk' (pCore 2 R) r))
    rw [quotientAction_mk, sectionEquiv_mk, sectionEquiv_mk, Model.sectionAut_mk]
    apply congrArg (QuotientGroup.mk' (pCore 2 (Model.residual x)))
    apply Subtype.ext
    exact d.subgroupMap_conjugation R M hRL hML m r
end CoverPointModel
end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearThree.MarkedAutomizer

end
