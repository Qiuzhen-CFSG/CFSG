module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentSieveAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedLinearTwoAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideLinearTwoSourceAt.Source

/-!
# All original component carriers, with only alternating-five containment open

The source sieve leaves a binary rank-one component or one of the permitted
carriers already containing the point residual. In the rank-one branch the
original contained Borel calculation or the original outside module theorem
forces field four. Thus every literal component quotient has a permitted
carrier. A component not containing the original point must be alternating
five. This proves the carrier half of 14.7.47 and isolates its remaining
containment duty without assuming it.
Source: Aschbacher--Smith 14.7.41--47, printed pp.1061--1063,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open OriginalComponentStatement WholeResidualAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
  (d : Counterexample T L)
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (hab : IsMulCommutative F.U)
  (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
  (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
  (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
  (C : Subgroup I) (hC : C.IsCComponent)
include d h hab structural previous faithful earlier hI hC

private theorem binary_model_four
    (n : ℕ) (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (2^n)) :
    Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  have hn2 : n = 2 := by
    by_cases hin : F.Li L 1 ≤ C.map I.subtype
    · obtain ⟨E,hEf,hEfin,hE,⟨e⟩⟩ := hm
      let : Fintype E := Fintype.ofFinite E
      let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
        (by simpa only [Nat.card_eq_fintype_card] using hE)
      exact local_linearTwo_contained_field_four_at d h hab structural previous faithful earlier
        I hI C hC hin hE (by omega) e
    · exact (OutsideLinearTwoSourceAt.local_binary_model_field_four_rank_ge_eight_at
        d h hab structural previous faithful earlier I hI C hC hin n (by omega) hm).1
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
  have hcard : Nat.card E = 4 := by simpa only [hn2,Nat.reducePow] using hE
  exact ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    hcard).some⟩

/-- Every literal original component quotient has one of the permitted
14.7.47 carriers, with no containment assumption or later source input. -/
theorem local_component_rows_at : ComponentRows (C ⧸ pCore 2 C) := by
  rcases local_component_binary_rank_one_or_rows_at d h hab structural previous faithful
    earlier I hI C hC with ⟨n,hn,hm⟩ | ⟨_,hc⟩
  · exact Or.inr (Or.inl ⟨5,by decide,by decide,
      binary_model_four d h hab structural previous faithful earlier I hI C hC n hn hm⟩)
  · exact hc

/-- Alternating five is the sole remaining carrier for an actual component
that does not contain the original point residual. -/
theorem local_component_outside_point_is_alternating_five_at
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype) :
    Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  rcases local_component_binary_rank_one_or_rows_at d h hab structural previous faithful
    earlier I hI C hC with ⟨n,hn,hm⟩ | ⟨hin,_⟩
  · exact binary_model_four d h hab structural previous faithful earlier I hI C hC n hn hm
  · exact (hout hin).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
