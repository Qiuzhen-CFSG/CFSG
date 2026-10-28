module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleComponentAction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SingleCubicAction

/-!
# Excluding the original single-factor case after every rechoice

The same selected normal component normalizes the original cubic span.
Its normalizer bound and the cubic Sylow supplement give the original
outside contradiction, discharging the single-product callback after every
S,I rechoice. Both Goldschmidt triples, the full O₃′ kernel and the literal
intersection are retained through that construction.

The nonsolvable generation bound and the original earlier-source inputs
remain explicit. This is not an unconditional 13.2.7 or 13.6.7 theorem.
Source: Aschbacher--Smith 13.2.7, printed pp.883--884.
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

/-- The original single-factor branch is excluded after every original
Sylow rechoice, without a product or normalization callback. -/
theorem terminal_model_of_original_single_exclusion
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
    (hparameter : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        ¬ Group.IsSolvable H →
        (pResidual 2 H).map H.subtype ∈ MainForward.faithfulLocalComponents S →
        (pResidual 2 H).map H.subtype ∈ Chapter1.LStar G (S : Subgroup G) →
        Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
          alternatingGroup (Fin 5)) →
        centralizer ((omegaOrbit S H).subgroupOf H : Set H) = pCore 2 H →
        1 < ChapterE.generationParameter H) :
    ClassificationModels.IsQTKEModel G := by
  apply terminal_model_of_original_paired_point_exclusion d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ J P Q q hSQ hg hqg hi hcore
  have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
  exact OriginalCentralization.single_original_quotient_false e hH hB hZ hSQ hg hqg hi hcore

/-- The single-factor omega-centralization conclusion after each original
S,I rechoice, with the multiple-overgroup guard transported from T. -/
theorem universal_single_outside_centralizes_omega
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G)
    (e : Context S I W W₁ W₂ W₃)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))) :
    H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) :=
  OriginalCentralization.single_outside_centralizes_omega e hH
    (universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e) he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
