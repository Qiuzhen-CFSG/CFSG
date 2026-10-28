module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLastModel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48OrdinaryLinearFive

/-!
# The original binary doubled witness has only the constrained case

All ordinary components are excluded on the literal original witness.
The original multiple-overgroup/non-FF source therefore produces a
constrained C-component with its actual fixed-space commutator and faithful
quotient action. Its further parabolic residual marking and constrained
module classification remain mathematical source duties.
Source: Aschbacher--Smith C.3.5 and C.4.8, pp.150--154.
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

/-- No ordinary component remains for the same original reciprocal witness. -/
theorem sourceOrbit_binary_witness_no_ordinary_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) : ¬ IsComponent H K := by
  intro hK
  exact D.sourceOrbit_binary_witness_ordinary_not_linear_five h hd F hF hmodel
    hw hWJ hJC K hK (D.sourceOrbit_binary_witness_ordinary_linear_five
      h hd F hF hmodel hw hWJ hJC K hK)

/-- The original hypotheses construct the constrained component, its whole
fixed-space commutator, and its faithful literal residual-quotient action. -/
theorem sourceOrbit_binary_reciprocal_constrained_action
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
        generalizedFitting K = pCore 2 K ∧
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
              (l : G) * (w : G) * (l : G)⁻¹ := by
  obtain ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,hLN,hcases⟩ :=
    D.sourceOrbit_binary_reciprocal_c48_action h hd hmany hnon F hF hmodel
  refine ⟨A,J,H,U,hw,hWJ,hJC,K,hK,hq,hout,hLN,?_⟩
  rcases hcases with ho | hc
  · exact (D.sourceOrbit_binary_witness_no_ordinary_component
      h hd F hF hmodel hw hWJ hJC K ho.1).elim
  · exact hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
