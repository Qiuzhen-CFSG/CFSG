module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.Complete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.Source13614
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.SourceReplacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.SourceTransport

/-!
# The original marked linear-three containment application

The original flag and earlier local conclusions supply the Sylow subgroup,
characteristic two and reduced module. The source component-invariance and
replacement theorems supply the Thompson commutator. Applying the completed
linear-three argument proves Lᵥ ≤ K on the literal original plus quotient.

Only the earlier A.3.12, universal 13.3.2 normalization and 13.6.3 centralizer
inputs remain beyond the original flag, local data and fusion. This is the
rank-one containment input used before the small-model exclusions and the
rank-four selection; it is not the full nonsingular-centralizer theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.14, 13.6.16 and 13.6.20, printed pp.929–931.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection A5Module ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original L₃(2) branch of 13.6.20, with all intervening component,
normalization, reduced-module and Thompson-action premises constructed. -/
theorem lv_le_and_noncentral_original_source
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
    (model : plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
      hL hz K ≃* Matrix.PSL3Two.PSL) :
    Lv L (markedV d.flag.module) ≤ K ∧
    ⁅plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) hL hz K,
      plusImage K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)
        hL hz (Lv L (markedV d.flag.module))⁆ ≠ ⊥ := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hred := WK_mem_reducedFamily_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK.1.1
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
  have hgen := (component_control_of_replacement_source T L standing h1332 h63
    (markedZ d.flag.module) (markedV d.flag.module) d.flag.z_central hvT
    (markedV_ne_one d.flag.module) hv2
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ d.flag_centralizer_index
    hchar K hK.1 hn hmove).2.2
  exact lv_le_and_noncentral_of_source standing d.flag c hA312 rfl earlier.T_normalizes_L
    hK hn hchar hgen hL hz hred model

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
