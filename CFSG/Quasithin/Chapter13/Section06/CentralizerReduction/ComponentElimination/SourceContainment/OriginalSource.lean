module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
public import Theory.GroupTheory.TwoLocalCharacteristicControl

/-!
# Original source assembly for the containment in 13.6.20

The original flag and preceding local results supply the Sylow, component
invariance, cubic residual quotient and reduced module on the literal
plus actor. Its seven-model catalogue gives the three-rank split.
The rank-two theta argument and the completed linear-three argument then
both put Lᵥ inside K.

This removes the separate local-application and rank-one normalization
premises from the source containment consumer. The specialized rank-two
proof discharges the A.3.18 application on the surviving models.
The earlier A.3.12, universal 13.3.2 normalization, 13.6.3 centralizer
condition and the reduced catalogue remain explicit.

The following 13.6.21 conclusion uses the earlier trivial two-core of
the join of K with T. If K lay in the maximal two-local M, the nontrivial
two-core of M would lie in that trivial core. This applies to every
selected K before the model or rank split.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14 and 13.6.18–20, printed pp.929–931.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment
open ComponentSelection A5Module ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The literal original containment, with the complete local application
constructed in both branches of the reduced-model rank split. -/
theorem lv_le_original_source_without_A318
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    Lv L (markedV d.flag.module) ≤ K := by
  have hv : orderOf (markedV d.flag.module) = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    refine ⟨?_, markedV_ne_one d.flag.module⟩
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  rcases RankTwo.source_rank_split_of_source standing hv hL hz hK model with hr | ⟨_, ⟨e⟩⟩
  · obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
      earlier standing.counterexample hfusion
    have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
      standing.counterexample hfusion K hK
    have hred := WK_mem_reducedFamily_original_source d V₃ earlier standing.qtke hm
      standing.counterexample hfusion K hK.1.1
    let s : RankTwo.LocalApplication.SourceInputs T K L
        (markedZ d.flag.module) (markedV d.flag.module) :=
      ⟨standing, hv, hK, hr, ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩,
        hn, hL, hz, c.residual_card, hred, model⟩
    exact (RankTwo.source_rank_two_without_A318
      (ChapterA.SQTKStructure.a36Input_of_theoremsAC
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hA312 s).2
  · exact (LinearThree.lv_le_and_noncentral_original_source d V₃ earlier standing hm
      hfusion hA312 h1332 h63 hK hL hz e).1

/-- The earlier conditional interface is preserved; its A.3.18 premise
is now redundant for this original reduced-model application. -/
theorem lv_le_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (_hA318 : RankTwo.EarlierA318ComponentCases.{u} KnownSimple.IsKnownSimple)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    Lv L (markedV d.flag.module) ≤ K :=
  lv_le_original_source_without_A318 d V₃ earlier standing hm hfusion hA312
    h1332 h63 hK hL hz model

/-- The original 13.6.21 conclusion for every selected component. Its
trivial join core and the maximal two-local property of M are derived
from the original earlier source data, without a model assumption. -/
theorem not_le_normalizer_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) :
    ¬ K ≤ normalizer (L : Set G) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hvT := d.V_le_T (map_mem d.flag.module
    (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v))
  have hv2 : markedV d.flag.module ^ 2 = 1 := by
    change d.flag.module.map (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
    rw [← map_pow]
    exact (congrArg d.flag.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans d.flag.module.map.map_one
  have hmove : ¬ K ≤ centralizer ({markedZ d.flag.module} : Set G) := by
    intro hc
    exact (invariant_component_consequences K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hK hn).1.2
      ((starPreimage_starImage_centralizes_seed_iff _ _ K hK.1.1).mpr hc)
  have hcore := (component_control_of_replacement_source T L standing h1332 h63
    (markedZ d.flag.module) (markedV d.flag.module) d.flag.z_central hvT
    (markedV_ne_one d.flag.module) hv2
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ d.flag_centralizer_index
    hchar K hK.1 hn hmove).1
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    have hmem : normalizer (L : Set G) ∈
        {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} := by
      rw [earlier.maximal_overgroups]
      exact Set.mem_singleton _
    exact hmem.1
  intro hKM
  obtain ⟨Q, hQ, hp, he⟩ := hM.prop
  have hQM : Q ≤ (normalizer (L : Set G)).pCoreIn 2 := by
    rw [he]
    exact le_pCoreIn_of_normalizes hp Q.le_normalizer le_rfl
  have hbound := pCoreIn_le_pCoreIn_of_sylow T
    (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)
    (sup_le hKM earlier.T_normalizes_L)
  rw [hcore] at hbound
  exact hQ (bot_unique (hQM.trans hbound))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment
