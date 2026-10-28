module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryRankTwo
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinarySporadic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryJanko

/-!
# The two remaining ordinary models for the original reciprocal witness

The whole-orbit rank-two argument and the Mathieu, Held and Janko exclusions
leave only PSL₅(2) and Ru as central quotients of an ordinary component.
The intended non-FF, multiple-overgroup branch produces the same reciprocal
witness with these bounds. Its constrained branch and the two surviving
ordinary module arguments remain open.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154, in the original
Chapter 12 non-FF doubled-binary source application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The same full central quotient has only the two remaining models. -/
theorem sourceOrbit_binary_witness_ordinary_linear_five_or_rudvalis
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
      Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := by
  rcases D.sourceOrbit_binary_witness_ordinary_five_or_sporadic
    h hd F hF hmodel hw hWJ hJC K hK with hm | ⟨name,hn,he⟩
  · exact Or.inl hm
  · rcases hn with rfl | rfl | rfl | rfl
    · exact (D.sourceOrbit_binary_witness_ordinary_not_mathieu
        h hd F hF hmodel hw hWJ hJC K hK he).elim
    · exact (D.sourceOrbit_binary_witness_ordinary_not_janko
        h hd F hF hmodel hw hWJ hJC K hK he).elim
    · exact (D.sourceOrbit_binary_witness_ordinary_not_held
        h hd F hF hmodel hw hWJ hJC K hK he).elim
    · exact Or.inr he

/-- Original source hypotheses construct the reciprocal witness and apply
the verified ordinary sieve; no local witness or classification is assumed. -/
theorem sourceOrbit_binary_reciprocal_ordinary_two_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ A J H U : Subgroup G, ∃ _hw : Witness L V A J H U,
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
        (H ⊓ normalizer (L : Set G)) LH (J.pCoreIn 2) D.sourceOrbit ∧
      ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
        (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
      ∀ K : Subgroup H, IsComponent H K →
        ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := by
  obtain ⟨_,_,_,_,_,A,_,_,_,_,_,J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_hypothesisC28 h hd hmany hnon F hF hmodel
  exact ⟨A,J,H,U,hw,hWJ,hJC,hc,hescape,fun K hK =>
    D.sourceOrbit_binary_witness_ordinary_linear_five_or_rudvalis
      h hd F hF hmodel hw hWJ hJC K hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
