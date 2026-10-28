module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.OffenderSubgroup
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import CFSG.Quasithin.ChapterB.QuasisimpleThompsonAction

/-!
# Quasisimple models on the actual offender actor

A normal quasisimple subgroup contained in the offender subgroup remains
quasisimple there. If its ambient quotient is a two-group and the ambient
two-core is trivial, it is exactly the generalized Fitting subgroup of the
actual offender actor. The genuine SQTK cover supplies the quasisimple
section hypothesis through A.2.1, and complete B.5.1 then classifies the
original module with this literal component. Thompson movement supplies
these inputs on the centralizer quotient used in source10.2.9.

Source: Aschbacher–Smith, B.1.11 and B.5.1, printed pp.73,99–103;
application in10.2.9, printed p.751.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

omit [Finite G] in
private theorem quotient_subgroupOf_isPGroup
    (L N : Subgroup G) [L.Normal] (hp : IsPGroup 2 (G ⧸ L)) :
    IsPGroup 2 (N ⧸ L.subgroupOf N) := by
  let f := (QuotientGroup.mk' L).comp N.subtype
  have hk : f.ker = L.subgroupOf N := by
    ext x
    change QuotientGroup.mk' L (x : G) = 1 ↔ (x : G) ∈ L
    exact QuotientGroup.eq_one_iff _
  exact ((hp.to_subgroup f.range).of_equiv
    (QuotientGroup.quotientKerEquivRange f).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hk)

/-- The two-group quotient identifies the actual component as the generalized
Fitting subgroup required by B.5.1 on the offender actor. -/
theorem quasisimple_offender_source_hypothesis {κ : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsQuasisimple L]
    (hLN : L ≤ offenderSubgroup ρ) (hsq : IsSQTK κ L)
    (hf : Function.Injective ρ) (hquot : IsPGroup 2 (G ⧸ L))
    (hcore : pCore 2 G = ⊥) :
    QuasisimpleSourceHypothesis (ρ.comp (offenderSubgroup ρ).subtype) κ
      (L.subgroupOf (offenderSubgroup ρ)) := by
  let N := offenderSubgroup ρ
  let D := L.subgroupOf N
  let e : D ≃* L := subgroupOfEquivOfLe hLN
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have htwo : pCore 2 N = ⊥ := SourceInduction.offenderSubgroup_twoCore ρ hcore
  have hfit : generalizedFitting N = D :=
    generalizedFitting_eq_of_quasisimple_two_quotient D
      (quotient_subgroupOf_isPGroup L N hquot) htwo
  refine ⟨inferInstance, hf.comp N.subtype_injective, inferInstance,
    (IsSQTK.equiv e).mpr hsq, ?_, htwo, offenderSubgroup_restrict_eq_top ρ⟩
  rw [hfit]
  exact (sup_eq_left.mpr (by
    rw [← hfit]
    exact (show center N ≤ fittingSubgroup N from le_sSup ⟨inferInstance,inferInstance⟩).trans
      (fitting_le_generalizedFitting N))).symm

/-- Complete known-simple B.5.1 retains the given component and module.
The SQTK hypothesis is inherited only by the quasisimple section. -/
theorem quasisimple_offender_source_conclusion
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal] [IsQuasisimple L]
    (hLN : L ≤ offenderSubgroup ρ)
    (c : SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple G)
    (hf : Function.Injective ρ) (hquot : IsPGroup 2 (G ⧸ L))
    (hcore : pCore 2 G = ⊥) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (L.subgroupOf (offenderSubgroup ρ))) := by
  let cL := c.subgroup L
  have hsq : IsSQTK KnownSimple.IsKnownSimple L :=
    SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) cL.sqtk
      (ChapterA.Section02.IsSectionOf.of_surjective cL.projection cL.projection_surjective)
  exact knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple
    SourceInduction.nonbinaryG2RootPairInput _ V _ _
    (quasisimple_offender_source_hypothesis ρ L hLN hsq hf hquot hcore)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion

namespace CFSG.Quasithin.ChapterB.InternalThompsonAction
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The literal component image and conjugation module in10.2.9 satisfy
all six B.5.1 clauses whenever the Thompson subgroup moves the module. -/
theorem quasisimple_source_conclusion_of_thompson_movement
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (P : Sylow 2 H) (K W : Subgroup H)
    [K.Normal] [W.Normal] [IsElementaryAbelian 2 W]
    (hK : K.IsCComponent) (hKP : K ⊔ (P : Subgroup H) = ⊤)
    (hcore : pCore 2 (ActionQuotient W) = ⊥)
    (hmove : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (W : Set H)) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((action W).comp (offenderSubgroup (action W)).subtype)
      ((K.map (actionMk W)).subgroupOf (offenderSubgroup (action W)))) := by
  let q := actionMk W
  let B := K.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : B.Normal := (inferInstance : K.Normal).map q hq
  let : IsQuasisimple B := quasisimple_of_thompson_movement
    SourceInduction.adequateClassification_knownSimple hH P K W hK hKP hcore hmove
  have hgen : (P : Subgroup H).map q ⊔ B = ⊤ := by
    change (P : Subgroup H).map q ⊔ K.map q = ⊤
    rw [←Subgroup.map_sup, sup_comm, hKP, map_top_of_surjective _ hq]
  have hquot : IsPGroup 2 (ActionQuotient W ⧸ B) :=
    quotient_isPGroup_of_sup_eq_top _ B (P.isPGroup'.map q) hgen
  let c : SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple (ActionQuotient W) :=
    { Cover := H
      kernel := centralizer (W : Set H)
      sqtk := hH
      equiv := MulEquiv.refl _ }
  exact QuasisimpleSource.SourceCompletion.quasisimple_offender_source_conclusion
    (action W) B (component_le_offenderSubgroup P K W hKP hcore hmove) c
    (action_faithful W) hquot hcore

end CFSG.Quasithin.ChapterB.InternalThompsonAction
