module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Thompson
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.Applications
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.Catalogue
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource

/-!
# The remaining outside branch in the actual A₅ classification consumer

In a putative counterexample to the Main-Theorem catalogue, 5.2.3 disposes
of every moving outside H with n(H)>1. Original 3.1.8 disposes of the branch
where J(T) centralizes the chosen A₅ module. Thus only n(H)≤1 with moving
J(T) remains in the outside-centralization input. This reduction is uniform
in the original Sylow and component, and supplies the literal universal
omega-centralizer application, including transport of the standing guard.

The final theorem consumes that reduction in the existing 13.6.7 and
terminal arguments. The completed prescribed-path replacement is supplied
directly to the existing small-quotient catalogue. The earlier Context
producer (qt-d-1332-source / qt-d-13512-source), C.1.32 producer
(qt-e-ms-small-ranktwo), and genuine 5.2.3 producer (qt-d-13627-components)
remain explicit. This task retains the low-parameter outside source proof;
qt-d-1361-source owns final classification assembly. No theorem here claims
unconditional 13.2.7 or the narrower two-model statement 13.6.1.

Source: Aschbacher--Smith 13.2.4(2), 13.2.7--8 and 13.6.7, pp.879--880,
928; 5.2.3, p.649; and the original small-quotient argument pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
open ChapterC Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original outside theorem is needed only in its moving-Thompson,
low-generation branch when proving the full Main-Theorem catalogue. -/
theorem outside_source_of_no_main_model
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hlow : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ centralizer (W : Set G) →
        ChapterE.generationParameter H ≤ 1 →
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G)) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) := by
  intro S I standing H hH
  obtain ⟨W,W₁,W₂,W₃,⟨d⟩⟩ := hcontexts S I standing
  by_contra hZ
  have hJ := OriginalCentralization.thompson_moves_of_omega_movement d hH hZ
  have hn : ChapterE.generationParameter H ≤ 1 := by
    by_contra! hn
    exact hno (main_model_of_source523_omega_movement d h523 hH hZ hn)
  exact hZ (hlow S I W W₁ W₂ W₃ d H hH hJ hn)

/-- Apply the reduction to the exact universal 13.6.3 callback. Context
normalization suffices here; the multiple-overgroup guard is transported
to S by the existing original-source application. -/
theorem universal_omega_centralizer_of_low_generation_outside
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hlow : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ centralizer (W : Set G) →
        ChapterE.generationParameter H ≤ 1 →
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G)) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥ := by
  intro S I standing
  obtain ⟨W,W₁,W₂,W₃,⟨d⟩⟩ := hcontexts S I standing
  apply omega_centralizer_of_original_outside_source S I standing d.normalizes_L
    _ (outside_source_of_no_main_model hno hcontexts h523 hlow S I standing)
  rwa [maximalTwoLocalOvergroups_ncard_sylow S T]

/-- The completed MS93 theorem supplies prescribed replacement on every
literal selected component, with no residual switching callback. -/
theorem original_source_path_replacement (L T : Subgroup G) (z v : G) :
    SourcePathReplacement L T z v := by
  intro K hK i t common hb a a' p hp
  exact BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource.prescribedReplacement
    common hb p hp

/-- The actual terminal Main-Theorem application with the high-generation
outside branch discharged by 5.2.3. Only the remaining original local branch
and the named independent earlier-source inputs are retained. -/
theorem terminal_model_of_low_generation_outside
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hlow : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ elementaryAbelianMaxJ (S : Subgroup G) ≤ centralizer (W : Set G) →
        ChapterE.generationParameter H ≤ 1 →
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G)) :
    ClassificationModels.IsQTKEModel G := by
  by_contra hno
  have ho := outside_source_of_no_main_model hno hcontexts h523 hlow
  have hB := baumann_normalizer d hc hmany (ho T L (standing d hc))
  have he := earlierLocal d hmany (ho T L (standing d hc)) (baumann_alternatives d) hB
  obtain ⟨_,hf,hform⟩ := configuration_of_outside_source d hc hmany (ho T L (standing d hc))
  have h63 := universal_omega_centralizer_of_low_generation_outside
    T hmany hno hcontexts h523 hlow
  apply hno
  apply terminal_model_of_context d hc hmany h1332 ho ?_ h523
  intro hfailure K hK
  exact reduced_catalogue_original_source_of_rankTwo_and_replacement rankTwo d.flag V₃ he
    (standing d hc) (moduleData d) hf hform hfailure h1332 h63 hK
    (normalizes_residual d) (centralizes_singular d)
    (original_source_path_replacement L (T : Subgroup G) _ _)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
