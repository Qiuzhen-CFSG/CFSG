module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.BinaryCases
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.ProjectedSeed
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalRecognition.Kernel
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.Constrained.Source

/-!
# The original recognized component and its moved-module alternatives

For either exchanged-plane size, the recognized L/O2(L) supplies the cubic
model facts and the genuine C.2.7 input. The actual U is elementary and reduced,
and B.5 classifies its moved section under its original centralizer quotient.
The original Q1 supplies a best offender on this very representation.

This proves the classification input to 15.1.28. The parabolic elimination
of the nonnatural alternatives, and the resulting natural coordinates and
projected point, remain necessary for the full natural-recognition theorem.

Source: Aschbacher--Smith 15.1.26--28, printed pp.1102--1103.
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

/-- Original 15.1.26 supplies the model facts required by C.2.7. -/
theorem HasExchangedLinearSource.cubicFacts {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource) : Facts (d.L ⧸ pCore 2 d.L) := by
  obtain ⟨n,hn,⟨mark⟩⟩ := s.2.2
  exact facts_of_small_binary_model (small_binary_model_of_marking hn mark)

/-- The recognized original component supplies C.2.7 without a NineSource
assumption or an additional characteristic-two premise. -/
theorem HasExchangedLinearSource.c27Input {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V) :
    Input KnownSimple.IsKnownSimple d.G1 d.Q1 d.MZ d.L :=
  d.constrained_input hG h s.1.quasisimple s.1.core_nontrivial s.1.characteristic_control
    s.1.core_normalizer s.cubicFacts s.2.1

/-- Elementary reducedness and the actual source splitting for both the
four- and sixteen-element planes, with all C.2.7 premises discharged. -/
theorem HasExchangedLinearSource.reduced_split {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    IsElementaryAbelian 2 (d.U t) ∧
      IsPReduced 2 ((d.U t).subgroupOf (d.L ⊔ d.S)) ∧
      IsPReduced 2 ((d.UL t).subgroupOf (d.L ⊔ d.S)) ∧
      d.U t = d.UL t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) := by
  let hi := s.c27Input hG h
  exact ⟨d.exchanged_U_elementary s.1 hG hM hu h hi s.cubicFacts t ht,
    d.exchanged_U_reduced s.1 hG hM hu h hi s.cubicFacts t ht,
    d.exchanged_UL_reduced s.1 hG hM hu h hi s.cubicFacts t ht,
    d.exchanged_U_split s.1 hG hM hu h hi s.cubicFacts t ht⟩

/-- The original moved module detects the full LS/O2(LS) action in either row. -/
theorem HasExchangedLinearSource.moved_action_kernel {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    let J := d.L ⊔ d.S
    centralizer ((d.UL t).subgroupOf J : Set J) = pCore 2 J :=
  (d.exchanged_UL_LS_centralizer_eq s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht).trans
    (d.exchanged_U_LS_centralizer_eq_pCore s.1 hG hM hu h
      (s.c27Input hG h) s.cubicFacts t ht htS)

/-- Once the natural-module geometry supplies a Sylow-fixed line, no extra
projection or stabilizer input is needed for the original recognized component. -/
theorem HasExchangedLinearSource.projected_point_of_fixed_line
    {d : CaseIComponentData T M Mc V} (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hline : Nat.card (d.UL t ⊓ centralizer (d.S : Set G) : Subgroup G) = 2) :
    ∃ ZU : Subgroup G, ZU ≤ d.UL t ∧ Nat.card ZU = 2 ∧
      ZU ≤ centralizer (d.S : Set G) ∧
      d.Z2 t ⊔ (d.U t ⊓ centralizer (d.L : Set G)) =
        ZU ⊔ (d.U t ⊓ centralizer (d.L : Set G)) ∧
      d.L ⊓ centralizer (ZU : Set G) = d.ML :=
  d.exchanged_projected_seed s.1 hG hM hu h (s.c27Input hG h) s.cubicFacts t ht htS hline

/-- Original 15.1.27 on the literal recognized component. The B.5 action
and moved cases use one section, and Q1's best offender uses the same quotient.
In particular source row (6) is retained throughout this construction. -/
theorem HasExchangedLinearSource.original_moved_cases {d : CaseIComponentData T M Mc V}
    (s : d.HasExchangedLinearSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    ∃ n : ℕ, ∃ hn : n = 4 ∨ n = 5,
      ∃ mark : (d.L ⧸ pCore 2 d.L) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2),
        let hf := facts_of_small_binary_model (small_binary_model_of_marking hn mark)
        let hi := d.constrained_input hG h s.1.quasisimple s.1.core_nontrivial
          s.1.characteristic_control s.1.core_normalizer hf s.2.1
        let J := d.L ⊔ d.Q1
        let W := (d.U t).subgroupOf J
        let hr := d.exchanged_U_reduced_on_LQ1 s.1 hG hM hu h hi hf t ht
        letI := hr.normal
        letI := hr.elementary
        let q := QuotientGroup.mk' (centralizer (W : Set J))
        let ρ := NormalElementaryQuotient.representation W q
          (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        let B := offenderSubgroup ρ
        (d.L.subgroupOf J).map q ≤ B ∧
          ∃ c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
            (ρ.comp B.subtype) (((d.L.subgroupOf J).map q).subgroupOf B),
            BinaryActor.ActionCase (ρ.comp B.subtype)
              (((d.L.subgroupOf J).map q).subgroupOf B) c.sectionData n ∧
            BinaryActor.MovedCase c.sectionData n ∧
            ∃ A : Subgroup J, A ∈ elementaryAbelianMaxSubgroups (d.Q1.subgroupOf J) ∧
              IsBestOffender ρ (A.map q) := by
  obtain ⟨n,hn,⟨mark⟩⟩ := s.2.2
  refine ⟨n,hn,mark,?_⟩
  intro hf hi J W hr
  let := hr.normal
  let := hr.elementary
  intro q ρ B
  obtain ⟨hKB,c,hc⟩ := d.exchanged_U_binary_action_cases s.1 hG hM hu h hi hf t ht htS hn mark
  exact ⟨hKB,c,hc,BinaryActor.movedCase hn hc,
    d.exchanged_U_best_offender s.1 hG hM hu h hi hf t ht htS⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
