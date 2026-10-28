module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionEightGeometryDecomposition
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FFSource
public import CFSG.Quasithin.Chapter3.Section02.QrcInput

/-!
# B.5.1 on the faithful point-span action

For the alternating-eight configuration, take the literal conjugation image of
LT on the point span. Its component is the image of L, obtained through L/O₂(L),
and its component quotient is a two-group. Reducedness of the point span removes
the actor's two-core. The SQTK hypothesis passes to the quasisimple component
using Theorem A for sections, so the given FF witness supplies the genuine B.5.1
source conclusion on the actual best-offender subgroup.

This prepares the moved-module identification in the companion module. The
point-span module structure remains an explicit input; no splitting or Irr⁺
condition on its moved space is assumed.

Source: Aschbacher--Smith, B.5.1 and the final paragraph of original 12.2.16,
printed pp.99 and 800, `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.AlternatingEightFusion
universe u
variable {G : Type u} [Group G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {C : AlternatingEightFusion T L V}
namespace PointSpanModule
variable (R : C.PointSpanModule)

/-- The literal conjugation image of LT on the point span. -/
abbrev actor := ChapterD.internalActionImage (L ⊔ (T : Subgroup G)) C.pointSpan R.normalizes

/-- The range restriction of the original action homomorphism. -/
def projection : (L ⊔ (T : Subgroup G) : Subgroup G) →* R.actor :=
  (ChapterD.UniqueFactor.actionHom _ _ R.normalizes).rangeRestrict

private theorem projection_surjective : Function.Surjective R.projection :=
  MonoidHom.rangeRestrict_surjective _

/-- The faithful binary representation of the actual conjugation image. -/
abbrev representation : letI := R.elementary
    Representation (ZMod 2) R.actor (Additive C.pointSpan) :=
  letI := R.elementary
  ChapterD.UniqueFactor.imageRepresentation _ _ R.normalizes

/-- The image of the original component L in the point-span actor. -/
abbrev component : Subgroup R.actor :=
  (L.subgroupOf (L ⊔ (T : Subgroup G))).map R.projection

/-- The original component maps onto its action image, with no chosen isomorphism. -/
def componentHom : L →* R.component :=
  (R.projection.subgroupMap (L.subgroupOf (L ⊔ (T : Subgroup G)))).comp
    (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm.toMonoidHom

theorem componentHom_surjective : Function.Surjective R.componentHom :=
  (R.projection.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe le_sup_left).symm.surjective

private theorem component_normal (D : ChosenModule T L V) : R.component.Normal := by
  let : (L.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact Normal.map inferInstance R.projection R.projection_surjective

private theorem component_ne_bot (D : ChosenModule T L V) : R.component ≠ ⊥ := by
  intro he
  have hc : L ≤ centralizer (C.pointSpan : Set G) := by
    intro l hl w hw
    have hm : R.projection ⟨l, (le_sup_left : L ≤ L ⊔ (T : Subgroup G)) hl⟩ ∈ R.component :=
      mem_map_of_mem _ hl
    have hh := congrArg (fun a : R.actor => (a.val ⟨w, hw⟩ : G)) (mem_bot.mp (he ▸ hm))
    change l * w * l⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply D.ne_bot
  apply le_bot_iff.mp
  calc
    V ≤ ⁅C.pointSpan, L⁆ := C.chosen_le_pointSpan_commutator D
    _ = ⊥ := by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hc

private theorem componentHom_core (D : ChosenModule T L V) : pCore 2 L ≤ R.componentHom.ker := by
  intro l hl
  apply Subtype.ext
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  change (l : G) * (w : G) * (l : G)⁻¹ = w
  have hc := C.componentCore_centralizes_pointSpan D R (mem_map_of_mem L.subtype hl) w w.property
  change (w : G) * (l : G) = (l : G) * (w : G) at hc
  rw [← hc, mul_inv_cancel_right]

private def componentQuotientHom (D : ChosenModule T L V) : (L ⧸ pCore 2 L) →* R.component :=
  QuotientGroup.lift _ R.componentHom (R.componentHom_core D)

private theorem componentQuotientHom_surjective (D : ChosenModule T L V) :
    Function.Surjective (R.componentQuotientHom D) :=
  QuotientGroup.lift_surjective_of_surjective _ R.componentHom
    R.componentHom_surjective (R.componentHom_core D)

private theorem component_quasisimple (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) : IsQuasisimple R.component := by
  let := hq
  let : Nontrivial R.component := (Subgroup.nontrivial_iff_ne_bot _).mpr (R.component_ne_bot D)
  exact IsQuasisimple.of_surjective (R.componentQuotientHom D)
    (R.componentQuotientHom_surjective D)

private theorem quotient_two (D : ChosenModule T L V) : letI := R.component_normal D
    IsPGroup 2 (R.actor ⧸ R.component) := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let := R.component_normal D
  have hp : IsPGroup 2 (H ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf H)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hx : X ≤ R.component.comap R.projection := fun _ hx => mem_map_of_mem _ hx
  exact hp.of_surjective (QuotientGroup.map _ _ R.projection hx)
    (QuotientGroup.map_surjective_of_surjective _ _ R.projection
      ((QuotientGroup.mk'_surjective _).comp R.projection_surjective) hx)

private theorem actor_core : pCore 2 R.actor = ⊥ :=
  Chapter3.Section02.internalActionImage_core_of_reduced _ _
    (R.le_sylow.trans le_sup_right) R.normalizes R.reduced

private theorem component_sqtk [Finite G] (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    IsSQTK KnownSimple.IsKnownSimple R.component := by
  let H := L ⊔ (T : Subgroup G)
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mp
      (h.join_sqtk.subgroup (L.subgroupOf H))
  let := R.component_quasisimple D h.quasisimple
  have hs : ChapterA.Section02.IsSemisimple R.component := by
    apply top_unique
    exact le_sSup (show IsComponent R.component ⊤ from
      ⟨Subgroup.IsSubnormal.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩)
  exact ⟨(show ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple L from
      ChapterA.Section02.theoremA_knownSimple).stronglyQuasithin_section
    hL.stronglyQuasithin hL.isKGroup
    (ChapterA.Section02.IsSectionOf.of_surjective R.componentHom R.componentHom_surjective) hs,
    hL.isKGroup.of_surjective R.componentHom R.componentHom_surjective⟩

/-- All B.5.1 source clauses for the faithful point-span action. -/
theorem source_conclusion [Finite G] (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := R.elementary
    R.component ≤ offenderSubgroup R.representation ∧
    Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (R.representation.comp (offenderSubgroup R.representation).subtype)
      (R.component.subgroupOf (offenderSubgroup R.representation))) := by
  let := R.elementary
  let := R.component_normal D
  let := R.component_quasisimple D h.quasisimple
  exact ChapterB.QuasisimpleSource.SourceCompletion.ff_quasisimple_source_conclusion
    R.representation R.component (R.quotient_two D) R.actor_core (R.component_sqtk D h)
    (ChapterD.UniqueFactor.imageRepresentation_injective _ _ R.normalizes) R.ff

end PointSpanModule

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.AlternatingEightFusion
