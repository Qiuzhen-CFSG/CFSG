module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLocal

/-!
# The original non-FF binary doubled witness with its ordinary source bounds

The intended multiple-overgroup and non-FF hypotheses supply the original
reciprocal witness and its C.2.8 configuration. Every ordinary component of
that same witness receives the literal quotient rank, residual section,
radical and normalizer information proved in the companion source files.
This is an application of those source increments; the remaining ordinary
families and constrained parabolic module rows are not excluded here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterA.Section02 ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original non-FF branch produces an actual reciprocal witness with
the proved ordinary quotient constraints, without a supplied local witness. -/
theorem sourceOrbit_binary_reciprocal_ordinary_source
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
        6 ≤ primeRank 2 (K ⧸ center K) ∧
        ((∃ f : ℕ, IsTheoremCRankTwoModel (K ⧸ center K) f) ∨
          ClassicalGroup.IsPSL (K ⧸ center K) 5 2 ∨
          ∃ name : SporadicName, (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
            Nonempty ((K ⧸ center K) ≃* name.Carrier)) ∧
        let X := (LH.subgroupOf H).subgroupOf K
        let R := ((J.pCoreIn 2).subgroupOf H).subgroupOf K
        let M := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
        let q := QuotientGroup.mk' (center K)
        IsPRadical 2 (R.map q) ∧
          (normalizer (R.map q : Set (K ⧸ center K))).comap q = normalizer (R : Set K) ∧
          normalizer (X.map q : Set (K ⧸ center K)) = M.map q := by
  obtain ⟨_,_,_,_,_,A,_,_,_,_,_,J,H,U,hw,hWJ,hJC,hc,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_hypothesisC28 h hd hmany hnon F hF hmodel
  refine ⟨A,J,H,U,hw,hWJ,hJC,hc,hescape,?_⟩
  intro K hK
  have hr := (D.sourceOrbit_binary_witness_ordinary_quotient h hd F hF hmodel hw hWJ hJC K hK).1
  have hm := D.sourceOrbit_binary_witness_ordinary_three_cases h hd F hF hmodel hw hWJ hJC K hK
  have hl := D.sourceOrbit_binary_witness_ordinary_local_normalizers
    h hd F hF hmodel hw hWJ hJC K hK
  exact ⟨hr,hm,hl.2.1,hl.2.2.1,hl.2.2.2.2.1⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
