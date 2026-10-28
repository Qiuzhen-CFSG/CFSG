module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OutsideIntrinsicSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalSylowNormalization
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.OriginalSylow
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource

/-!
# The literal nonsingular centralizer from the intrinsic outside source

At every selected Sylow, the genuine earlier module clause constructs the
original Context. The intrinsic outside analysis supplies centralization,
and actual conjugacy supplies normalization. The selected MS pair has its
original Sylow witness, so its proved classification and prescribed
replacement give the literal nonsingular-point centralizer bound.

The original module family and two-model exclusion remain explicit.
There is no earlier 5.2.3 classifier or universal MS classification premise.
Source: Aschbacher--Smith 13.6.1--7 and 13.6.22--23, pp.926--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentReduction InitialSieve
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section03.SourceCompletion Section03.A5Setup.OriginalMaximality
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private theorem intrinsic_outside_at_every_original_sylow
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) := by
  intro S I hs H hH
  have hmS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  obtain ⟨a⟩ := hs.a5
  obtain ⟨W,W₁,W₂,W₃,_,⟨e⟩⟩ := exists_context_from_original_modules
    (sourceHypothesis_hypothesis1331 hs) a hmS (hmodules S I hmS)
  exact original_outside_centralizes_omega_without_source523 e hmS (hmodules S I hmS) hH

/-- The actual nonsingular-point centralizer is contained in the original
module normalizer using only the original module family and local exclusions. -/
theorem original_nonsingular_centralizer_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : ∀ (S : Sylow 2 G) (I : Subgroup G),
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        OriginalAlternatingFiveModules1332At S I)
    (hc : IsA5Counterexample G) :
    centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G) := by
  have h1332 := original_normalization_at_every_sylow d hmany
  have h1327 := intrinsic_outside_at_every_original_sylow T hmany hmodules
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

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
