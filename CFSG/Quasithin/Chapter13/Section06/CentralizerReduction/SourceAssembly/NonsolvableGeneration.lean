module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SingleExclusion
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.ResidualFive

/-!
# The exact remaining generation obstruction in the original outside branch

The original nonsolvable moving H has a faithful residual with literal A5
core quotient. The new generation calculation places n(H) in {1,2}.
In a counterexample to the final catalogue, the original 5.2.3 application
excludes value two. Thus every elementary subgroup of the same residual
has image of order at most two under H -> H/O2(H), after every original
Sylow/component rechoice.

An actual elementary lift with image order four discharges the original
hparameter premise in the terminal consumer. Its ambient construction
remains with this assembly owner; no quotient-parameter equality or
unconditional 13.2.7/13.6.7 is asserted. Earlier Context, 13.3.2, genuine
C.1.32 and 5.2.3 retain their existing producers and final discharge.

Source: Aschbacher--Smith 13.2.8(1), printed p.880, and the terminal
13.6.7 application, pp.928--934; E.1.2--6 and E.1.14(1), pp.209--214.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open A5Module ComponentSelection ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open Section05.A5Source Section02.A5Outside
open TerminalContradiction.Components.SuzukiIsolation
open ChapterC Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Positive attainment and the upper bound for the original nonsolvable H. -/
theorem original_nonsolvable_generation_bounds
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    1 ≤ ChapterE.generationParameter H ∧ ChapterE.generationParameter H ≤ 2 := by
  obtain ⟨_,⟨e⟩⟩ := OriginalCentralization.nonsolvable_residual_faithful_A5 d hn hH hZ hs
  exact ChapterE.ValuesEvenClassical.ResidualFive.parameter_bounds (T.subtype hH.1.1.2) e

/-- The precise residual image obstruction when the original parameter is small. -/
theorem original_low_parameter_residual_images
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) (hlow : ChapterE.generationParameter H ≤ 1) :
    ChapterE.generationParameter H = 1 ∧
      ∀ A : Subgroup H, IsElementaryAbelian 2 A → A ≤ pResidual 2 H →
        Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
  obtain ⟨_,⟨e⟩⟩ := OriginalCentralization.nonsolvable_residual_faithful_A5 d hn hH hZ hs
  have hb := ChapterE.ValuesEvenClassical.ResidualFive.parameter_bounds (T.subtype hH.1.1.2) e
  refine ⟨by omega,?_⟩
  intro A hA hAR
  let := hA
  exact ChapterE.ValuesEvenClassical.ResidualFive.residual_elementary_image_card_le_two
    (T.subtype hH.1.1.2) e hlow A hAR

/-- The surviving obstruction after every original rechoice. The earlier
source guards construct the Context and normalize its faithful components. -/
theorem universal_original_low_parameter_residual_images
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ChapterE.generationParameter H = 1 ∧
      ∀ A : Subgroup H, IsElementaryAbelian 2 A → A ≤ pResidual 2 H →
        Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) ≤ 2 := by
  obtain ⟨W,W₁,W₂,W₃,⟨d⟩⟩ := hcontexts S I standing
  have hlow : ChapterE.generationParameter H ≤ 1 := by
    by_contra! hgt
    exact hno (main_model_of_source523_omega_movement d h523 hH hZ hgt)
  exact original_low_parameter_residual_images d
    (normalizes_faithful_of_source1332 d h1332) hH hZ hs hlow

/-- An actual residual elementary lift discharges hparameter in the original
terminal consumer, preserving its full source data and multiple-overgroup guard. -/
theorem terminal_model_of_original_residual_lifts
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
    (hlifts : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        ¬ Group.IsSolvable H →
        (pResidual 2 H).map H.subtype ∈ MainForward.faithfulLocalComponents S →
        (pResidual 2 H).map H.subtype ∈ Chapter1.LStar G (S : Subgroup G) →
        Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
          alternatingGroup (Fin 5)) →
        centralizer ((omegaOrbit S H).subgroupOf H : Set H) = pCore 2 H →
        ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
          Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) :
    ClassificationModels.IsQTKEModel G := by
  apply terminal_model_of_original_single_exclusion d hc hmany h1332 hcontexts rankTwo h523
  intro S I W W₁ W₂ W₃ e H hH hZ hs hfaith hmax hquot hker
  obtain ⟨A,hA,hAR,hcard⟩ := hlifts S I W W₁ W₂ W₃ e H hH hZ hs hfaith hmax hquot hker
  let := hA
  obtain ⟨a⟩ := hquot
  have hn := ChapterE.ValuesEvenClassical.ResidualFive.parameter_two_of_residual_A5_lift
    (S.subtype hH.1.1.2) a A hAR hcard
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
