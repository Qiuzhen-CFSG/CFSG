module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.SourceReplacement
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import Theory.GroupTheory.MaximalTwoLocalTransport

/-!
# The original omega-centralizer input from the outside-source theorem

The uniform A₅ hypothesis makes the selected faithful component maximal.
The known-simple A/C theorems give its unique maximal two-local normalizer
once the earlier normalization theorem is applied. The actual multiple-
overgroup standing hypothesis supplies a minimal outside local subgroup.
Original 13.2.7 centralizes the Sylow omega in that subgroup, so uniqueness
forces C_{Ω₁Z(T)}(L)=1. Normality in T then gives C_T(L)=1.

The construction is uniform in the Sylow subgroup: the cardinality premise
transports by Sylow conjugacy. The actual 13.6.16 consumer below consequently
requires only the earlier normalization and outside-centralization theorems,
without a separate 13.6.3 callback or chosen-module/local-configuration input.
Original 13.2.7 remains a genuine earlier source obligation.

Source: Aschbacher–Smith 13.2.7, 13.3.5(2), 13.6.3 and 13.6.16,
printed pp.880, 886, 926 and 930; the standing assumption after 2.1.1.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceTransferFields.HigherFieldParabolics
variable {G : Type*} [Group G] [Finite G]

/-- Original 13.6.3(2), with maximality, uniqueness and the outside witness
constructed from the original standing hypotheses. -/
theorem omega_centralizer_of_original_outside_source
    (T : Sylow 2 G) (L : Subgroup G) (standing : SourceHypothesis T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨e⟩ := standing.a5
  have hmax := Section03.A5Setup.OriginalMaximality.maximal_local
    (sourceHypothesis_hypothesis1331 standing) e
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    standing.qtke T hmax
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L _ L le_rfl hTL)
      (le_componentOrbit L _)
  have hM : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [horbit] using hu.normalizer_maximal
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany _ hM hTL)
  apply centralizer_omega_eq_bot_of_earlier_source (T : Subgroup G) L
    (normalizer (L : Set G)) H T.isPGroup' ?_ hH.1.2 (h1327 H hH)
  simpa only [horbit] using hu.normalizer_unique

/-- The same original source input gives the full Sylow centralizer used
by the replacement-component argument. -/
theorem sylow_centralizer_of_original_outside_source
    (T : Sylow 2 G) (L : Subgroup G) (standing : SourceHypothesis T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1327 : ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ :=
  centralizer_T_eq_bot_of_omega (T : Subgroup G) L T.isPGroup' hTL
    (omega_centralizer_of_original_outside_source T L standing hTL hmany h1327)

/-- Construct the literal universal 13.6.3 callback from the original
earlier-source implications, transporting the standing guard to each Sylow. -/
theorem universal_omega_centralizer_of_original_outside_source
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h1327 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G)) :
    ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥ := by
  intro S I standing
  apply omega_centralizer_of_original_outside_source S I standing
    (h1332 S I (sourceHypothesis_hypothesis1331 standing))
    _ (h1327 S I standing)
  rwa [maximalTwoLocalOvergroups_ncard_sylow S T]

/-- The actual 13.6.16 application needs no independent omega-centralizer
premise once original 13.2.7 is supplied. -/
theorem component_control_of_original_outside_source
    (T : Sylow 2 G) (L : Subgroup G) (standing : SourceHypothesis T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h1327 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (z v : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ ∧
      CharacteristicNormalizerObstruction (Tv (T : Subgroup G) v) K ∧
      K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) v)⁆ :=
  component_control_of_replacement_source T L standing h1332
    (universal_omega_centralizer_of_original_outside_source T hmany h1332 h1327)
    z v hz hvT hv hv2 hSylow hidx hchar K hK hS hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
