module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.NaturalLayer

/-!
# The natural cover on the characteristic replacement

The new omega orbit supplies a fresh FF offender. The original C-component,
its quotient marking and SQTK hypothesis transfer to the literal replacement
quotient image. Natural recognition therefore applies there at the original
field degree, and identifies its moving omega orbit with the moved central
omega layer. The canonical projection retains its fixed central kernel.

These are the local module hypotheses needed after the minimum replacement
in MS93 Section 7. They do not impose the original odd-index radical condition
on the replacement and do not assume an inner ambient quotient.
Source: MS93 (3.2)(vi), pp.863--866, and Section 7, pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- All component structure holds on its literal image in the new core quotient. -/
theorem Input.replacement_component_image_structure :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    (K.subgroupOf d.overgroup).Normal ∧ C.Normal ∧ IsSimpleGroup C ∧ IsQuasisimple C ∧
      centralizer (C : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ := by
  let := h.replacement_quotient_simple d
  exact MSCentralOrbit.component_image_structure _ _ (h.replacement_component d)
    (h.replacement_two_group d) (h.replacement_product d)

omit [Finite F] [CharP F 2] in
/-- The order of the replacement's component image retains the original marking. -/
theorem Input.replacement_component_image_card_sp :
    Nat.card ((K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))) =
      Nat.card (Matrix.symplecticGroup (Fin 2) F) :=
  (Nat.card_congr (cComponentTwoCoreQuotientEquiv
    (h.replacement_component d)).symm.toEquiv).trans
    (Nat.card_congr (h.replacement_quotientEquiv d).toEquiv)

omit [Finite F] [CharP F 2] in
/-- SQTK transfers through the original component and its two-group kernel. -/
theorem Input.replacement_component_image_sqtk :
    IsSQTK KnownSimple.IsKnownSimple
      ((K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))) := by
  let A := K.subgroupOf d.overgroup
  have hk := (h.sqtk.subgroup d.overgroup).subgroup A
  have hq : IsSQTK KnownSimple.IsKnownSimple (A ⧸ pCore 2 A) := by
    refine ⟨?_,hk.isKGroup.quotient (pCore 2 A)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 A) pCore_isPGroup]
    exact hk.stronglyQuasithin p hp ho
  exact (IsSQTK.equiv (cComponentTwoCoreQuotientEquiv (h.replacement_component d))).mp hq

/-- The replacement's own Thompson subgroup supplies its FF offender. -/
theorem Input.replacement_centralOmega_isFFModule :
    IsFFModule (NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) :=
  MSCentralOrbit.centralOmega_isFFModule d.radical (h.replacement_characteristic d)
    (h.replacement_two_group d) (h.replacement_radical_ne_bot d)
    (h.replacement_core_le d) (h.replacement_core_selfCentralizing d)
    (h.replacement_omegaOrbit_centralizer d) (QuotientGroup.mk' (pCore 2 d.overgroup))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- The literal omega-center action has natural moved quotient of degree n.
The source hypotheses supply faithfulness, SQTK and all FF premises. -/
theorem Input.replacement_centralOmega_moved_natural :
    let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
    let : C.Normal := (h.replacement_component_image_structure d).2.1
    let ρ := NormalElementaryQuotient.representation
      (omegaCenterIn (pCore 2 d.overgroup)) (QuotientGroup.mk' (pCore 2 d.overgroup))
      (QuotientGroup.mk'_surjective _)
      ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
    IsIrrPlus ρ C (subspaceCommutator ρ ⊤ C) ∧
      ∃ E : BinaryField, E.degree = n ∧
        Nonempty (ActionEquiv ((MovedSection.ofNormal ρ C).action.comp C.subtype)
          (binarySymplectic E)) := by
  obtain ⟨hK,hC,hs,hq,hcent⟩ := (h.replacement_component_image_structure d)
  let := hK
  let := hC
  let := hs
  let := hq
  dsimp only
  apply ff_card_sp_moved_natural _ _ F h.field_card h.nonbinary
    (h.replacement_component_image_card_sp d) hcent (h.replacement_component_image_sqtk d)
  · exact NormalElementaryQuotient.representation_injective _ _ _ _
  · exact (h.replacement_centralOmega_isFFModule d)

/-- The original omega orbit and full central omega layer have the same
literal commutator with K; no fully moved or field-four premise is needed. -/
theorem Input.replacement_initialCore_eq :
    ⁅omegaOrbit d.radical,K.subgroupOf d.overgroup⁆ = ⁅omegaCenterIn (pCore 2 d.overgroup),K.subgroupOf d.overgroup⁆ := by
  let C := (K.subgroupOf d.overgroup).map (QuotientGroup.mk' (pCore 2 d.overgroup))
  obtain ⟨_,hC,hs,hq,_⟩ := (h.replacement_component_image_structure d)
  let := hC
  let := hs
  let := hq
  let : IsElementaryAbelian 2 (omegaOrbit d.radical) :=
    omegaOrbit_elementary d.radical (h.replacement_core_le d) (h.replacement_core_selfCentralizing d)
  have hne : C ≠ ⊥ := by
    intro hz
    have hc := (h.replacement_component_image_card_sp d)
    have hlo := card_symplectic_ge F h.field_card h.nonbinary
    change Nat.card C = _ at hc
    rw [hz,card_bot] at hc
    omega
  exact NormalElementaryQuotient.commutator_eq_of_irrPlus (omegaOrbit d.radical)
    (omegaCenterIn (pCore 2 d.overgroup))
    (omegaOrbit_le_centralOmega d.radical (h.replacement_core_le d) (h.replacement_core_selfCentralizing d))
    (QuotientGroup.mk' (pCore 2 d.overgroup)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_omegaOrbit_centralizer d).symm)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)
    (K.subgroupOf d.overgroup) C rfl hne (h.replacement_centralOmega_moved_natural d).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
