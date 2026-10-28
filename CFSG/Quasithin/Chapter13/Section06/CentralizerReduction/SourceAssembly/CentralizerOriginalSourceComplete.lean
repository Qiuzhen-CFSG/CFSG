module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OutsideGeometryOriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalSylowNormalization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.OriginalSylow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalCatalogue

/-!
# The original nonsingular centralizer from the actual source theorems

At every selected Sylow, the genuine earlier module clause constructs the
original Context. The proved solvable and nonsolvable outside cases give
omega-centralization, while actual Sylow conjugacy gives normalization.
The selected C.1.32 pair has its original Sylow witness; its proved block
classification and the prescribed MS replacement eliminate the small rows.
The orthogonal endgame yields the literal nonsingular centralizer bound.

The full Main-Theorem model follows on the same original flag and singular
line. The earlier module family and genuine5.2.3 remain explicit; there is
no universal MS classification, Context or centralizer premise.
Source: Aschbacher--Smith13.6.1--7,13.6.22--23, pp.926--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section03.SourceCompletion Section03.A5Setup.OriginalMaximality
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem outside_at_every_original_sylow
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) := by
  intro S I hs H hH
  have hmS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨a⟩ := hs.a5
  obtain ⟨W,W₁,W₂,W₃,_,⟨e⟩⟩ := exists_context_from_original_modules
    (sourceHypothesis_hypothesis1331 hs) a hmS (hmodules S I hmS)
  exact original_outside_centralizes_omega_from_modules e hmS (hmodules S I hmS)
    h523 hno hH

/-- The literal nonsingular-point centralizer is contained in the original
module normalizer after every local source duty has been discharged. -/
theorem original_nonsingular_centralizer_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G) :
    centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G) := by
  have hc : IsA5Counterexample G :=
    ⟨fun hu => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.unitary_binary hu)).toQTKEModel),
     fun hl => hno ((ClassificationModels.IsTheoremDModel.exceptional
      (.linear_three hl)).toQTKEModel)⟩
  have h1332 := original_normalization_at_every_sylow d hmany
  have h1327 := outside_at_every_original_sylow T hmany hmodules h523 hno
  have ho := h1327 T L (standing d hc)
  have hB := baumann_normalizer d hc hmany ho
  have he := earlierLocal d hmany ho (baumann_alternatives d) hB
  obtain ⟨_,hf,hform⟩ := configuration_of_outside_source d hc hmany ho
  apply centralizer_le_normalizer_of_original_sylow_source d.flag V₃ he
    (standing d hc) (moduleData d) hf hform h1332
    (universal_omega_centralizer_of_original_outside_source T hmany h1332 h1327)
    (normalizes_residual d) (centralizes_singular d)
  intro K hK i t common hb a a' p hp
  exact ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource.prescribedReplacement
    common hb p hp

/-- The full Main-Theorem catalogue follows from the genuine original
Context, earlier module family and earlier5.2.3 classifier. -/
theorem original_context_model_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    ClassificationModels.IsQTKEModel G := by
  by_contra hno
  exact hno (TerminalContradiction.source_qtkeModel_of_A5_context d
    (original_nonsingular_centralizer_from_modules d hmany hmodules h523 hno)
    (original_singular_escape_from_modules d hmany (hmodules T L hmany) h523 hno) h523)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
