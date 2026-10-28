module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.Source
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.NormalCover
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization.SylowRigidity
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOrdinary.Source
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete

/-!
# Containment in the original L₃(2) component

The noncentral plus action places Lᵥ in a normal containing component D of
the actual plus actor. The A.3.6 description of the image of D modulo the
actor's two-core and Sylow rigidity show that Lᵥ normalizes K. The original
equivariant projection then lifts to Lᵥ ≤ K.

This discharges ambient normalization in the rank-one branch of 13.6.20.
The complete known-simple A/C and B.5 theorems supply the structural and
module classifications; A.3.12 and the earlier marked local data remain
the genuine preceding source inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.20, printed p.931, and A.3.6–8, pp.43–46.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection A5Module Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
    {K L M V V₁ V₂ : Subgroup G} {T : Sylow 2 G}

private theorem a36_knownSimple : A36Input.{u} KnownSimple.IsKnownSimple :=
  ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)

private theorem quasisimple_classification :
    ChapterB.SourceInduction.ProjectiveLine.QuasisimpleClassificationInput.{u,u}
      KnownSimple.IsKnownSimple :=
  ChapterB.QuasisimpleSource.SourceCompletion.knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple) a36_knownSimple
    ChapterB.SourceClassification.irreducibleClassification_knownSimple
    ChapterB.SourceInduction.nonbinaryG2RootPairInput

/-- The original linear-three containment with ambient normalization and
all A.3.6, A.3.8 and B.5 classification inputs discharged. -/
theorem lv_le_and_noncentral_of_source
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hM : M = normalizer (L : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ f.module) (markedV f.module))
    (hn : Tv (T : Subgroup G) (markedV f.module) ≤ normalizer (K : Set G))
    (hchar : generalizedFitting (Gv (markedV f.module)) = pCore 2 (Gv (markedV f.module)))
    (hgen : K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV f.module))⁆)
    (hL : Tv (T : Subgroup G) (markedV f.module) ≤
      normalizer (Lv L (markedV f.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV f.module) ≤
      centralizer ({markedZ f.module} : Set G))
    (hred : WK K L (T : Subgroup G) (markedZ f.module) (markedV f.module) ∈
      Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) (markedV f.module)))
    (model : plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
      hL hz K ≃* Matrix.PSL3Two.PSL) :
    Lv L (markedV f.module) ≤ K ∧
    ⁅plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module) hL hz K,
      plusImage K L (T : Subgroup G) (markedZ f.module) (markedV f.module)
        hL hz (Lv L (markedV f.module))⁆ ≠ ⊥ := by
  have hcomm := CentralAction.plus_commutator_ne_bot_of_source standing f c hM hTL hK hn
    hchar hgen hL hz model quasisimple_classification
    ChapterB.SourceInduction.adequateClassification_knownSimple
  obtain ⟨D, hD, _, hKD, hLD, _, hsup⟩ :=
    AmbientNormalization.exists_normal_cover_of_source standing f c hA312
      (fun _ _ _ => ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple)
      hK hn hL hz hred model hcomm
  let A := plusActor K L (T : Subgroup G) (markedV f.module)
  have hv : orderOf (markedV f.module) = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    refine ⟨?_, markedV_ne_one f.module⟩
    change f.module.map _ ^ 2 = 1
    rw [← map_pow]
    exact (congrArg f.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans f.module.map.map_one
  have hAG : A ≤ Gv (markedV f.module) :=
    plusActor_le_Gv K L (T : Subgroup G) (markedV f.module) hK.1.1
  have hsq : IsSQTK KnownSimple.IsKnownSimple A :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hAG)).mp
      ((standing.qtke.involution_centralizer_sqtk hv).subgroup
        (A.subgroupOf (Gv (markedV f.module))))
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (A ⧸ pCore 2 A) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 A) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := A)
  have ha := a36_knownSimple (A ⧸ pCore 2 A) hsqQ (pCore_quotient_pCore_eq_bot 2)
    (D.map (QuotientGroup.mk' (pCore 2 A))) (hD.map_quotient _)
  have hLK := AmbientNormalization.SylowRigidity.normalizes_of_A36 K L
    (T : Subgroup G) (markedZ f.module) (markedV f.module) hK
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ hn hL
    D hD hKD hLD hsup c.residual_card ha
  exact ⟨lv_le_of_noncentral_of_normalizes K L (T : Subgroup G) (markedZ f.module)
    (markedV f.module) hL hz hK hn model c.residual_card hcomm hLK, hcomm⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
