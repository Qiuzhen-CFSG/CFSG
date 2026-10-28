module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalLayer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGeneric

/-!
# The original moved-layer quotient and escaping Cartan prime pair

Apply the natural alternative of source 5.1.3 to the literal moved layer
of the original omega-span. Sylow-fixed generation extends its quotient
marking to the whole span. The symmetric-five alternative contradicts the
faithful original Cartan action, so the common-normal argument makes H
centralize omega in every degree, including degree two. Uniqueness removes
the fixed kernel and supplies a full natural model on that same omega-span.

The degree bound gives two or four and the actual escaping prime pair,
with its original Cartans, residual, Sylow, Hall markings and PSL3(4)
exclusion. Exhaustive module selection and recognition of the resulting
zero-core pair remain with the local-to-global assembly.

Source: Aschbacher--Smith 5.1.3(3), 5.1.6(2), 5.2.2 and 12.2.2,
pp.630--632,647,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- The source moved-layer natural quotient gives a full original omega-span
model, centralization in every degree, and the literal escaping prime pair. -/
theorem rankOne_cartan_natural_layer_degree_and_prime_pair_of_escape
    {T : Sylow 2 G} {L V H A B : Subgroup G} {n : ℕ}
    (C : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n) (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G))
    (hm : IsNaturalFixedQuotient L
      (layer L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)) n) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n ∧
      H ≤ omegaCentralizer T ∧
      IsNaturalModule L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n ∧
      ∃ (p : ℕ) (D R : Subgroup G), CartanPrimeActor A H p D ∧
        LocalData T L H B D R ∧ SelectedSourceModels H R ∧
        (generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) := by
  let hi := C.rankOne_generic_input_of_many h hmany (by omega : 1 < n) hpsl
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  obtain ⟨hdegree,hs⟩ := hi.natural_layer_quotient_cartan_degree_and_smallGeneration hH hgen c hm hz
  obtain ⟨hHC,_,hmodel⟩ := hi.natural_layer_quotient_cartan_model hH hgen c hm hz
  obtain ⟨p,D,hd⟩ := hs.exists_prime_actor hcontrol hescape
  obtain ⟨R,d,hselected,hzero,hf⟩ := source_prime_pair_zero_core hi hH hgen hthree c hd
  exact ⟨hdegree,hs,hHC,hmodel,p,D,R,hd,d,hselected,hzero,hf⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
