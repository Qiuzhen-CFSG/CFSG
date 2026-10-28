module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Classification
public import Theory.GroupTheory.ReducedNormal.QuasisimpleImage

/-!
# The original component quotient on the chosen constrained module

The original noncentral reduced module U detects L/O2(L). Its centerless
quotient marking therefore transfers to the actual component in the B5
conclusion, with the image of every original element retained. This supplies
model comparison on the same U and quotient used by the best offender.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The actual L-image on U has exactly the original centerless quotient,
and its marking commutes with the original quotient map. -/
theorem U_component_marking (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    ∃ e : (d.L ⧸ pCore 2 d.L) ≃* (d.L.subgroupOf J).map q,
      ∀ l : d.L, ((e (QuotientGroup.mk' (pCore 2 d.L) l)) : J ⧸ centralizer (W : Set J)) =
        q ⟨l,(show d.L ≤ J from le_sup_left) l.property⟩ := by
  intro J W hr
  let := hr.normal
  let K := d.L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le d.L.le_normalizer hi.normalizes)
  let eK : K ≃* d.L := subgroupOfEquivOfLe (show d.L ≤ J from le_sup_left)
  have hmap : (pCore 2 K).map eK = pCore 2 d.L := pCore_map_iso 2 eK
  let e0 := QuotientGroup.congr _ _ eK hmap
  let := hi.quasisimple
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv e0.symm
  have hz : center (K ⧸ pCore 2 K) = ⊥ := (Facts.of_equiv e0 hf).1
  have hUJ : d.U t ≤ J := (d.U_le_Q1 s hG hM hu h hi hf t ht).trans le_sup_right
  have hm : ⁅W,K⁆ ≠ ⊥ := by
    intro he
    have hh := congrArg (map J.subtype) he
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,
      map_subgroupOf_eq_of_le (show d.L ≤ J from le_sup_left),Subgroup.map_bot] at hh
    exact d.Z2_not_centralizes_L s hM hu h t ht htS
      ((le_conjugateSpanBy _ _).trans (commutator_eq_bot_iff_le_centralizer.mp hh))
  let e := e0.symm.trans (reducedQuasisimpleImageEquiv W K hr hz hm)
  refine ⟨e,?_⟩
  intro l
  have he0 : e0.symm (QuotientGroup.mk' (pCore 2 d.L) l) =
      QuotientGroup.mk' (pCore 2 K) (eK.symm l) := by
    apply e0.injective
    rw [MulEquiv.apply_symm_apply]
    change QuotientGroup.mk' (pCore 2 d.L) l =
      QuotientGroup.mk' (pCore 2 d.L) (eK (eK.symm l))
    rw [MulEquiv.apply_symm_apply]
  change ((reducedQuasisimpleImageEquiv W K hr hz hm)
    (e0.symm (QuotientGroup.mk' (pCore 2 d.L) l)) : J ⧸ centralizer (W : Set J)) = _
  rw [he0,reducedQuasisimpleImageEquiv_apply]
  rfl

/-- Full B5 and the quotient marking use one literal component and module. -/
theorem U_marked_moved_section (d : CaseIComponentData T M Mc V) (s : d.NineSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (d.L.subgroupOf J).map q ≤ B ∧
      Nonempty (ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B)) ∧
      Nonempty ((d.L ⧸ pCore 2 d.L) ≃* (((d.L.subgroupOf J).map q).subgroupOf B)) := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  obtain ⟨hKB,hs⟩ := d.U_moved_section s hG hM hu h hi hf t ht htS
  obtain ⟨e,_⟩ := d.U_component_marking s hG hM hu h hi hf t ht htS
  exact ⟨hKB,hs,⟨e.trans (subgroupOfEquivOfLe hKB).symm⟩⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
