module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Residual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryPlacedJankoExcluded.Unconditional

/-!
# The original doubled-binary C.4.8 witness after native exclusions

The native Janko-four cover and the proved Rudvalis exclusion remove both
ordinary native alternatives from the original odd-local obstruction.
The same reciprocal witness consequently satisfies C.2.8 on the whole
source orbit, with its generalized-Fitting escape and quotient maps retained.
The parabolic residual marking and the C.4.8 module classification remain
separate mathematical obligations; neither is assumed in this extraction.

Source: Aschbacher--Smith 4.4.3, printed pp.622--623, and C.4.8,
printed pp.153--154, in the original Chapter 12 doubled-orbit application.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.Section04.BinaryThreeNaturalDualExclusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual reciprocal witness satisfies C.2.8 and escapes the original
normalizer, with both native component alternatives discharged. -/
theorem sourceOrbit_binary_reciprocal_hypothesisC28
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ∃ A : Subgroup G,
        A ≤ H ∧ A ≤ centralizer (D.sourceOrbit : Set G) ∧ Nat.card A = p ∧
        ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
        ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
        ∃ J P W : Subgroup G, Witness L V A J P W ∧
          D.sourceOrbit ≤ J.pCoreIn 2 ∧
          J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
          ChapterC.HypothesisC28 KnownSimple.IsKnownSimple P
            (P ⊓ normalizer (L : Set G))
            ((solvableResidual (L ⊓ P : Subgroup G)).map (L ⊓ P).subtype)
            (J.pCoreIn 2) D.sourceOrbit ∧
          ¬ (generalizedFitting (P ⧸ pCore 2 P)).comap
            (QuotientGroup.mk' (pCore 2 P)) ≤ (normalizer (L : Set G)).subgroupOf P := by
  obtain ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hnot,J,P,W,hw,hWJ,hJC,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_obstruction_of_janko_cover
      Janko4.LocalStructure.PureFirstNormalizers.CompleteCover.maximalTwoLocalCover
      h hd hmany hnon F hF hmodel
  exact ⟨H,hH,p,hp,hpo,A,hAH,hAC,hcard,hout,hnot,J,P,W,hw,hWJ,hJC,
    D.sourceOrbit_binary_witness_hypothesisC28 h hd F hF hmodel hw hWJ hJC,hescape⟩

/-- The original multiple-overgroup witness supplies the C.4.8 escape. In the
constrained branch its actual fixed-space commutator is elementary, contains
the whole doubled orbit, and has a faithful action of the literal quotient
LH R/R. No native cover, parabolic marking or module-classification premise
is added. The ordinary component alternative remains explicit. -/
theorem sourceOrbit_binary_reciprocal_c48_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ A J H U : Subgroup G, ∃ hw : Witness L V A J H U,
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let R := J.pCoreIn 2
      let M := H ⊓ normalizer (L : Set G)
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ M.subgroupOf H ∧ LH ≤ normalizer (K.map H.subtype : Set G) ∧
        ((IsComponent H K ∧ LH.subgroupOf H ≤ K ∧ D.sourceOrbit.subgroupOf H ≤ K) ∨
         (generalizedFitting K = pCore 2 K ∧
          Input KnownSimple.IsKnownSimple H R M (K.map H.subtype) ∧
          let Q := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
          let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
          D.sourceOrbit ≤ W ∧ W ≤ Q ∧ LH ≤ normalizer (W : Set G) ∧
            W ≤ centralizer (LH.pCoreIn 2 : Set G) ∧
            (centralizer (W : Set G)).subgroupOf LH = pCore 2 LH ∧
            IsElementaryAbelian 2 W ∧
          let := normal_subgroupOf_sup_of_le_normalizer
            ((le_conjugateSpanBy LH M).trans hw.2.2.2.2.2.2.1.span_normalizes_radical)
          ∃ ρ : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) →* MulAut W,
            Function.Injective ρ ∧
            ∀ (l : LH) (w : W), (ρ (radicalQuotientMap LH R l) w : G) =
              (l : G) * (w : G) * (l : G)⁻¹)) := by
  obtain ⟨_,_,_,_,_,A,_,_,_,_,_,J,H,U,hw,hWJ,hJC,_,hescape⟩ :=
    D.sourceOrbit_binary_reciprocal_hypothesisC28 h hd hmany hnon F hF hmodel
  obtain ⟨K,hK,hq,hout,hLN,hcases⟩ :=
    D.sourceOrbit_binary_witness_c48_source_reduction h hd F hF hmodel hw hWJ hJC hescape
  refine ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,hLN,?_⟩
  rcases hcases with ho | ⟨hfK,hi,hWS,hWQ,hnW⟩
  · exact Or.inl ho
  · have hc := D.sourceOrbit_binary_witness_fixed_moved_centralizer h hd F hF hmodel
      hw hWJ hJC K hK hq hout hfK
    have ha := D.sourceOrbit_binary_witness_fixed_moved_action h hd F hF hmodel
      hw hWJ hJC K hK hq hout hfK
    exact Or.inr ⟨hfK,hi,hWS,hWQ,hnW,hc.1,hc.2,ha.1,ha.2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
