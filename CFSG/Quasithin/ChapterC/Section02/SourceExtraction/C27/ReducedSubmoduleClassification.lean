module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.ReducedSubmoduleOffender
/-!
# Full B5 on a specified reduced C.2.7 submodule

The reduced noncentral module has the original component image as its
quasisimple generalized Fitting subgroup. Its actual radical best offender
places that image in the offender subgroup. The full proved B5 source theorem
then classifies the moved section of this same action.

Source: Aschbacher--Smith C.2.7 and 15.1.27--28, pp.146,1102--1103.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
/-- Full B.5.1 for the same reduced submodule and original component image. -/
theorem moved_section_on_reduced_submodule
    (hi : Input KnownSimple.IsKnownSimple H R M K)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (hr : IsPReduced 2 W) (hWR : W ≤ R.subgroupOf (K ⊔ R))
    (hm : ⁅W,K.subgroupOf (K ⊔ R)⁆ ≠ ⊥) :
    let q := QuotientGroup.mk' (centralizer (W : Set (K ⊔ R : Subgroup G)))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (K.subgroupOf (K ⊔ R)).map q ≤ B ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((K.subgroupOf (K ⊔ R)).map q).subgroupOf B)) := by
  let J := K ⊔ R
  let K0 := K.subgroupOf J
  let R0 := R.subgroupOf J
  let C := centralizer (W : Set J)
  let q := QuotientGroup.mk' C
  let ρ := NormalElementaryQuotient.representation W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let B := offenderSubgroup ρ
  let Kstar := K0.map q
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer hi.normalizes)
  let e : K0 ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let := hi.quasisimple
  let : IsQuasisimple (K0 ⧸ pCore 2 K0) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hp : IsPGroup 2 R := by
    have hh := hi.setup.radical.isPGroup.map H.subtype
    rwa [map_subgroupOf_eq_of_le hi.setup.radical_le] at hh
  obtain ⟨P,hRP⟩ := hp.comap_subtype.exists_le_sylow (P := R0)
  have hgen : K0 ⊔ R0 = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left) (show R ≤ J from le_sup_right),subgroupOf_self]
  have hprod : ∀ g : J, ∃ k ∈ K0, ∃ t ∈ (P : Subgroup J), k*t=g := by
    intro g
    obtain ⟨k,hk,t,ht,he⟩ := mem_sup_of_normal_left.mp (hgen.symm ▸ mem_top g)
    exact ⟨k,hk,t,hRP ht,he⟩
  obtain ⟨_,hfit,hquasi⟩ := internalModule_quasisimple_structure W q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    hr.quotient_pCore_eq_bot P K0
    (hi.component.2.subgroupOf_of_le le_sup_left hi.join_le) inferInstance hm hprod
  let : IsQuasisimple Kstar := hquasi
  obtain ⟨A,_,hA⟩ := best_offender_on_reduced_submodule hi W hr hWR hm
  let Astar := A.map q
  let : B.Normal := offenderSubgroup_normal ρ
  let : IsElementaryAbelian 2 Astar := hA.1.2
  have hshape : IsQuasisimple (generalizedFitting (J ⧸ C)) := hfit ▸ hquasi
  have hBF := generalizedFitting_normal_eq_of_quasisimple_or_three hr.quotient_pCore_eq_bot
    (Or.inl hshape) B Astar (IsElementaryAbelian.isPGroup 2 Astar) hA.1.1
    (hA.le_offenderSubgroup ρ)
  rw [←hfit] at hBF
  have hKB : Kstar ≤ B := hBF.ge.trans (map_subtype_le _)
  have hfitB : generalizedFitting B = Kstar.subgroupOf B := by
    apply map_injective B.subtype_injective
    rw [hBF,map_subgroupOf_eq_of_le hKB]
  have hcoreB : pCore 2 B = ⊥ := by
    apply ((pCore 2 B).map_eq_bot_iff_of_injective B.subtype_injective).mp
    apply bot_unique
    exact (show (pCore 2 B).map B.subtype ≤ pCore 2 (J ⧸ C) from
      le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map _⟩).trans
      hr.quotient_pCore_eq_bot.le
  let D := Kstar.subgroupOf B
  let eD : D ≃* Kstar := subgroupOfEquivOfLe hKB
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv eD.symm
  have hsqK : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hi.component.1)).mp
      (hi.setup.sqtk.subgroup (K.subgroupOf H))
  have hsq : IsSQTK KnownSimple.IsKnownSimple Kstar :=
    ChapterB.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) hsqK
      (ChapterA.Section02.IsSectionOf.of_surjective
        ((q.subgroupMap K0).comp e.symm.toMonoidHom)
        ((q.subgroupMap_surjective K0).comp e.symm.surjective))
  have hsource : ChapterB.QuasisimpleSource.QuasisimpleSourceHypothesis
      (ρ.comp B.subtype) KnownSimple.IsKnownSimple D := by
    refine ⟨inferInstance,(NormalElementaryQuotient.representation_injective W q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)).comp B.subtype_injective,
      inferInstance,(IsSQTK.equiv eD).mpr hsq,?_,hcoreB,offenderSubgroup_restrict_eq_top ρ⟩
    rw [hfitB]
    exact (sup_eq_left.mpr (by
      rw [←hfitB]
      exact (show center B ≤ fittingSubgroup B from le_sSup ⟨inferInstance,inferInstance⟩).trans
        (fitting_le_generalizedFitting B))).symm
  refine ⟨hKB,?_⟩
  exact ChapterB.QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    ChapterB.SourceClassification.irreducibleClassification_knownSimple
    ChapterB.SourceInduction.nonbinaryG2RootPairInput _ _ _ _ hsource
end CFSG.Quasithin.ChapterC.C27Source
