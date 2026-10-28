module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicSpan
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SingleCubicInverter

/-!
# The cubic quotient action and span normalizer after every original rechoice

The actual separating Sylow element centralizes the selected cubic and
inverts the Borel residual image. Its odd five-point action forces the
same cubic to centralize the marked I/O₂(I) quotient. The original
Sylow-conjugate span is normalized by I; its nontrivial two-core and
uniqueness over IS bound the full span normalizer by N_G(I).

These conclusions are supplied after each original S,I rechoice, preserving
both Goldschmidt triples, the O₃′ quotient, literal intersection, zero
quotient two-core and multiple-overgroup guard. The remaining callback
must establish the component's normalization of that span and the final
contradiction. Nonsolvable generation and the original earlier-source
premises remain explicit; this is not unconditional 13.2.7 or13.6.7.

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

/-- Each original rechoice supplies the trivial cubic action on the literal
A₅ quotient and the full normalizer bound for its actual conjugate span. -/
theorem terminal_model_of_original_cubic_action
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
      ∀ e : Context S I W W₁ W₂ W₃,
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
        ∀ hn : c.cubic_lift.map J.subtype ≤ normalizer (I : Set G),
        ¬ c.cubic_lift.map J.subtype ≤
          centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Nat.card ((pResidual 2 (P.map q)).map (P.map q).subtype) = 3 →
        ∀ t : J, (t : G) ∈ (S : Subgroup G) →
          (t : G) ∈ centralizer (c.cubic_lift.map J.subtype : Set G) →
          q t ∉ centralizer ((pResidual 2 (P.map q)).map (P.map q).subtype : Set _) →
          (∀ a ∈ (pResidual 2 (P.map q)).map (P.map q).subtype,
            q t * a * (q t)⁻¹ = a⁻¹) →
          (∀ (y : G) (hy : y ∈ c.cubic_lift.map J.subtype),
            e.quotientNormalizerAction ⟨y,hn hy⟩ = 1) →
          normalizer (conjugateSpanBy (c.cubic_lift.map J.subtype)
            (S : Subgroup G) : Set G) ≤ normalizer (I : Set G) → False)
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
  apply terminal_model_of_original_cubic_inverter d hc hmany h1332 hcontexts
    rankTwo h523 ?_ hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ J P Q q hSQ hg hqg hi hcore prod hn hm
    hcard t ht htD htR hinv
  have hact := OriginalCentralization.single_cubic_quotient_action_eq_one e prod
    hqg hcore hH.1.1.2 hn t ht htD htR
  have hB := universal_baumann_normalizer_of_many T hmany S I W W₁ W₂ W₃ e
  exact hproduct S I W W₁ W₂ W₃ e H hH hZ hSQ hg hqg hi hcore prod hn hm
    hcard t ht htD htR hinv hact
    (OriginalCentralization.single_cubic_span_normalizer_le e hH hB hZ hg prod hn hact)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
