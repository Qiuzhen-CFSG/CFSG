module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinarySieve
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryRudvalis

/-!
# The last ordinary model for the original doubled-binary witness

The genuine whole-orbit exclusions leave PSL5(2) as the only possible
central quotient of an ordinary component of the original reciprocal
witness. The original non-FF/multiple-overgroup prefix constructs that
witness. The PSL5 module source and the constrained case remain separate.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every ordinary component has the remaining linear-five central quotient. -/
theorem sourceOrbit_binary_witness_ordinary_linear_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : IsComponent H K) :
    ClassicalGroup.IsPSL (K ⧸ center K) 5 2 := by
  rcases D.sourceOrbit_binary_witness_ordinary_linear_five_or_rudvalis
    h hd F hF hmodel hw hWJ hJC K hK with hm | hm
  · exact hm
  · exact (D.sourceOrbit_binary_witness_ordinary_not_rudvalis
      h hd F hF hmodel hw hWJ hJC K hK hm).elim

/-- Original source hypotheses construct the reciprocal witness and apply
the verified ordinary sieve; no local witness or classification is assumed. -/
theorem sourceOrbit_binary_reciprocal_ordinary_linear_five
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
        ClassicalGroup.IsPSL (K ⧸ center K) 5 2 := by
  obtain ⟨_,_,_,_,_,A,_,_,_,_,_,J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_hypothesisC28 h hd hmany hnon F hF hmodel
  exact ⟨A,J,H,U,hw,hWJ,hJC,hc,hescape,fun K hK =>
    D.sourceOrbit_binary_witness_ordinary_linear_five
      h hd F hF hmodel hw hWJ hJC K hK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
