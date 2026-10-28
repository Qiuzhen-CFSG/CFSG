module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Homogeneous.SourceCore
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates

/-!
# The literal moved space and its fixed supplement

The quotient representation of the original L Q₁ action has moved space
exactly [U,L]. The source splitting U = [U,L] C_U(LS) supplies an invariant
supplement for the full offender-generated actor.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Identify the literal moved space and its supplement, with the original
quotient map and without restricting the exchanged-plane size. -/
theorem HasExchangedLinearSource.original_moved_space_and_supplement
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    let K := ((d.L.subgroupOf J).map q).subgroupOf B
    ∀ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp B.subtype) K,
      (∀ v : Additive W, v ∈ c.sectionData.space.toSubmodule ↔ (v.toMul.val : G) ∈ d.UL t) ∧
      c.sectionData.space.toSubmodule ⊔ Representation.invariants (ρ.comp B.subtype) = ⊤ := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B K c
  have hUJ : d.U t ≤ J := (d.exchanged_U_le_Q1 s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht).trans le_sup_right
  have hLJ : d.L ≤ J := le_sup_left
  obtain ⟨hKB,_⟩ := d.exchanged_U_moved_section s.1 hG hM hu h
    (s.c27Input hG h) s.cubicFacts t ht htS
  have he : c.sectionData.space.toSubmodule =
      NormalElementaryQuotient.commutatorSpace W (d.L.subgroupOf J) := by
    rw [c.sectionData.space_eq]
    change subspaceCommutator (ρ.comp B.subtype) ⊤ K = _
    rw [subspaceCommutator_comp_map, map_subgroupOf_eq_of_le hKB]
    exact (NormalElementaryQuotient.commutatorSpace_eq W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) _).symm
  have hcomm : (⁅W,d.L.subgroupOf J⁆ : Subgroup J).map J.subtype = d.UL t := by
    rw [map_commutator,map_subgroupOf_eq_of_le hUJ,map_subgroupOf_eq_of_le hLJ]
    rfl
  have hmem (v : Additive W) : v ∈ c.sectionData.space.toSubmodule ↔
      (v.toMul.val : G) ∈ d.UL t := by
    rw [he]
    change v.toMul.val ∈ (⁅W,d.L.subgroupOf J⁆ : Subgroup J) ↔ _
    rw [← hcomm]
    exact (mem_map_iff_mem J.subtype_injective).symm
  refine ⟨hmem,top_unique ?_⟩
  intro v _
  have hv : (v.toMul.val : G) ∈ d.U t := v.toMul.property
  rw [d.exchanged_U_split_LS s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht] at hv
  let := d.exchanged_U_elementary s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht
  let C := d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G)
  have hv' : (⟨(v.toMul.val : G),v.toMul.property⟩ : d.U t) ∈
      (d.UL t).subgroupOf (d.U t) ⊔ C.subgroupOf (d.U t) := by
    rw [← subgroupOf_sup (d.UL_le_U t) (show C ≤ d.U t from inf_le_left)]
    exact hv
  obtain ⟨u,huU,f,hf,heq⟩ := Subgroup.mem_sup_of_normal_right.mp hv'
  let u' : Additive W := Additive.ofMul ⟨⟨u.val,hUJ u.property⟩,u.property⟩
  let f' : Additive W := Additive.ofMul ⟨⟨f.val,hUJ f.property⟩,f.property⟩
  apply Submodule.mem_sup.mpr
  refine ⟨u',(hmem u').mpr huU,f',?_,?_⟩
  · intro b
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective (centralizer (W : Set J)) b.val
    change ρ b.val f' = f'
    rw [← ha]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    have haD : (a : G) ∈ d.L ⊔ d.S :=
      (sup_le le_sup_left ((d.exchanged_Q1_le_S s.1 hu).trans le_sup_right)) a.property
    exact mul_inv_eq_iff_eq_mul.mpr (hf.2 a haD)
  · apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : d.U t => (z : G)) heq
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
