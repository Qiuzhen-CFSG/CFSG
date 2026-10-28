module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Action
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.ModelRestriction

/-!
# Original 15.1.27 for both exchanged source rows

The compatible L/O2(L) marking narrows the B.5 action classification to
binary degree four or five. The actual moved space retains the natural,
orthogonal-cover, exterior, natural-plus-dual, and repeated-natural
alternatives. Eliminating the nonnatural alternatives is the separate
parabolic argument in 15.1.28.

Source: Aschbacher--Smith 15.1.27--28, printed pp.1102--1103.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01
open Theory.SpecificGroups.BinaryComponentResidual ChapterA.Section05To06 Section03 Section03.InitialSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The complete B.5.1 classification on the original U, narrowed by the
original component quotient marking, without an image-recognition premise. -/
theorem exchanged_U_binary_action_cases (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (mark : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (d.L.subgroupOf J).map q ≤ B ∧
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B),
        BinaryActor.ActionCase (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B)
          c.sectionData n := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B
  obtain ⟨hKB,⟨c⟩,⟨e⟩⟩ := d.exchanged_U_marked_moved_section s hG hM hu h hi hf t ht htS
  exact ⟨hKB,c,BinaryActor.actionCase _ hn (e.symm.trans mark) c.clause_one⟩

/-- The source 15.1.27 models of the actual moved module, with its natural,
augmentation-cover, irreducible degree-ten, and bounded-sum actions retained. -/
theorem exchanged_U_binary_moved_cases (d : CaseIComponentData T M Mc V) (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hi : Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L)
    (hf : Facts (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (mark : (d.L ⧸ pCore 2 d.L) ≃* SL(n,ZMod 2)) :
    let J := d.L ⊔ d.Q1
    let W := (d.U t).subgroupOf J
    let hr := d.exchanged_U_reduced_on_LQ1 s hG hM hu h hi hf t ht
    letI := hr.normal
    letI := hr.elementary
    let q := QuotientGroup.mk' (centralizer (W : Set J))
    let ρ := NormalElementaryQuotient.representation W q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    let B := offenderSubgroup ρ
    (d.L.subgroupOf J).map q ≤ B ∧
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B),
        BinaryActor.MovedCase c.sectionData n := by
  intro J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B
  obtain ⟨hKB,c,hc⟩ := d.exchanged_U_binary_action_cases s hG hM hu h hi hf t ht htS hn mark
  exact ⟨hKB,c,BinaryActor.movedCase hn hc⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
