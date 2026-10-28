module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.RecognizedInput
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Splitting
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.ActionKernel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.MovedModule
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.ModelRestriction

/-!
# The constrained module from a recognized original Nine component

The original fixed-plane argument supplies characteristic two and the genuine
C.2.7 input for the recognized small binary component. The chosen exchanged
line then generates a split reduced module with a nonzero moved seed. Its
component image retains the original quotient marking and satisfies the full
B5 source conclusion. No independent fitting, reducedness, splitting or
component-image isomorphism is required.

The exhaustive earlier component catalogue and the subsequent natural-module
selection and contradiction remain separate source obligations.

Source: Aschbacher--Smith 15.1.26--28, printed pp.1102--1103.
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

/-- The source split and moved seed from the recognized component, with all
C.2.7 and cubic Facts premises discharged. -/
theorem NineSource.small_binary_split_seed {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.U t = d.UL t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) ∧
      ∃ z ∈ d.Z2 t, z ≠ 1 ∧ ∃ u ∈ d.UL t, u ≠ 1 ∧
        u ∈ centralizer (d.S : Set G) ∧
        u * z ∈ d.U t ⊓ centralizer ((d.L ⊔ d.S : Subgroup G) : Set G) ∧
        d.L ⊓ centralizer ({u} : Set G) = d.L ⊓ centralizer (d.Z2 t : Set G) ∧
        d.L ⊓ centralizer ({u} : Set G) ≤ d.ML := by
  let hi := s.c27Input_of_small_binary_model hG hM hu h he
  let hf := facts_of_small_binary_model he
  exact ⟨d.U_split s hG hM hu h hi hf t ht,
    d.Z2_moved_seed s hG hM hu h hi hf t ht htS⟩

/-- The source's actual nonzero moved line with its original component
centralizer bound, after recognition discharges C.2.7 and cubic Facts. -/
theorem NineSource.small_binary_moved_line {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧
      d.L ⊓ centralizer (ZU : Set G) = d.L ⊓ centralizer (d.Z2 t : Set G) ∧
      d.L ⊓ centralizer (ZU : Set G) ≤ d.ML :=
  d.Z2_moved_line s hG hM hu h
    (s.c27Input_of_small_binary_model hG hM hu h he)
    (facts_of_small_binary_model he) t ht htS

theorem small_binary_model_of_marking {Q : Type*} [Group Q]
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (mark : Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    SmallBinaryOrdinaryModel Q := by
  refine Or.inl ⟨n,hn,?_⟩
  exact ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
    ⟨mark.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

/-- All B5 alternatives for the actual marked binary component and original
U, with fitting, C.2.7 and cubic model facts derived internally. -/
theorem NineSource.small_linear_action_cases {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (mark : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    let he := small_binary_model_of_marking hn mark
    let hi := s.c27Input_of_small_binary_model hG hM hu h he
    let hf := facts_of_small_binary_model he
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
      ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B),
        ChapterB.QuasisimpleSource.SourceCompletion.BinaryActor.ActionCase
          (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B) c.sectionData n :=
  d.U_binary_action_cases s hG hM hu h
    (s.c27Input_of_small_binary_model hG hM hu h (small_binary_model_of_marking hn mark))
    (facts_of_small_binary_model (small_binary_model_of_marking hn mark)) t ht htS hn mark

/-- Moving by the original component preserves the exact faithful LS quotient. -/
theorem NineSource.small_binary_moved_action_kernel {d : CaseIComponentData T M Mc V}
    (s : d.NineSource) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (he : SmallBinaryOrdinaryModel (d.L ⧸ pCore 2 d.L))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.S
    centralizer ((d.UL t).subgroupOf J : Set J) = pCore 2 J :=
  (d.UL_LS_centralizer_eq s hG hM hu h
    (s.c27Input_of_small_binary_model hG hM hu h he)
    (facts_of_small_binary_model he) t ht).trans
      (s.small_binary_action_kernel hG hM hu h he t ht htS)

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
