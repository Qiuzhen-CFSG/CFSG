module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedModels
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedBinaryG2
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedAlternatingSeven
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryExcluded

/-!
# The two remaining linear star models on the original binary witness

All ordinary components and the other constrained star models are excluded
from the original reciprocal source. The selected constrained component
has star image A8 = SL4(2) or SL5(2), with the whole original six-space
inside its literal star module. The remaining task is the actual parabolic
residual and module restriction in these two linear cases.
Source: Aschbacher--Smith C.4.8 and 12.1.11, pp.153--154,794.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Only the binary degree-four and degree-five linear star models remain. -/
theorem sourceOrbit_binary_witness_constrained_linear_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
    Nonempty (C ≃* alternatingGroup (Fin 8)) ∨
      Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  rcases D.sourceOrbit_binary_witness_constrained_four_models
    h hd F hF hmodel hw hWJ hJC K hK hq hout hfK with hg | ha | hr
  · exact (D.sourceOrbit_binary_witness_constrained_not_binary_g2
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK hg).elim
  · exact (D.sourceOrbit_binary_witness_constrained_not_alternating_seven
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK ha).elim
  · exact hr

/-- The original hypotheses produce a constrained component with one of
the two remaining linear models and the whole orbit in its actual star module. -/
theorem sourceOrbit_binary_reciprocal_constrained_linear_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : D.SourceOrbitNonFF)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F) :
    ∃ A J H U : Subgroup G, ∃ _hw : Witness L V A J H U,
      D.sourceOrbit ≤ J.pCoreIn 2 ∧
      J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        generalizedFitting K = pCore 2 K ∧
        Input KnownSimple.IsKnownSimple H (J.pCoreIn 2)
          (H ⊓ normalizer (L : Set G)) (K.map H.subtype) ∧
        D.sourceOrbit ≤ (starV (K.map H.subtype) (J.pCoreIn 2)).map
          (K.map H.subtype ⊔ J.pCoreIn 2).subtype ∧
        let C := starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype)
        Nonempty (C ≃* alternatingGroup (Fin 8)) ∨
          Nonempty (C ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) := by
  obtain ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,_,hfK,hi,hW,hWQ,_⟩ :=
    D.sourceOrbit_binary_reciprocal_constrained_action h hd hmany hnon F hF hmodel
  exact ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,hfK,hi,hW.trans hWQ,
    D.sourceOrbit_binary_witness_constrained_linear_models
      h hd F hF hmodel hw hWJ hJC K hK hq hout hfK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
