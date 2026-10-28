module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicNormalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SingleProduct

/-!
# The moving cubic lift after every original Sylow rechoice

The order-three lift in the original Goldschmidt product moves the full
omega-center and lies in the original component normalizer. These are
proved with the literal O₃′ quotient and the same selected lift. The
multiple-overgroup guard supplies the independent Baumann bound at each
rechoice.

The remaining single-factor callback receives these proved conclusions;
it retains the original join, both triples, intersection and zero two-core.
The final quotient-action contradiction, nonsolvable generation bound and
genuine earlier source inputs remain explicit. This is not unconditional
13.2.7 or 13.6.7. Source: Aschbacher--Smith 13.2.7, pp.883--884.
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

/-- Every original rechoice supplies a moving cubic lift in N_G(I) for
the remaining single-factor contradiction. -/
theorem terminal_model_of_original_cubic_normalizer
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
    (hproduct : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        let J := H ⊔ borelResidual S I
        let P := (borelResidual S I ⊔ (S : Subgroup G)).subgroupOf J
        let Q := H.subgroupOf J
        let q := QuotientGroup.mk' (pPrimeCore 3 J)
        IsSQTK KnownSimple.IsKnownSimple J →
        ChapterF.IsGoldschmidtTriple P Q →
        ChapterF.IsGoldschmidtTriple (P.map q) (Q.map q) →
        P.map q ⊓ Q.map q = ((S : Subgroup G).subgroupOf J).map q →
        pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ →
        ∀ c : OriginalCentralization.SingleQuotientProduct S I H,
        c.cubic_lift.map J.subtype ≤ normalizer (I : Set G) →
        ¬ c.cubic_lift.map J.subtype ≤
          centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) → False)
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
  apply terminal_model_of_original_single_product d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ J P Q q hSQ hg hqg hi hcore prod
  have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
  exact hproduct S I W W₁ W₂ W₃ e H hH hZ hSQ hg hqg hi hcore prod
    (OriginalCentralization.single_cubic_le_normalizer e hH hB hZ hg prod)
    (OriginalCentralization.single_cubic_moves_omega hH hZ hg prod)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
