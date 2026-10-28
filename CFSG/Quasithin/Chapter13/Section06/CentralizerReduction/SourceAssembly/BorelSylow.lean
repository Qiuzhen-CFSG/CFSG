module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BorelQuotient
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SingleAmalgam

/-!
# The original Borel-join quotient exclusion in the terminal A5 argument

The literal Borel-core Sylow calculation, Thompson and Baumann heredity,
Stellmacher normal-supplement transfer, and common-normal contradiction
now discharge 13.2.13 from the earlier Baumann bound and solvability.
This removes the separate quotient-exclusion or Sylow-transfer premise
from the universal original outside-centralization application.

The independent Baumann normalizer bound, paired join-core argument,
nonsolvable generation bound and final amalgam exclusion remain with
qt-d-1367-assembly. The earlier Context, 13.3.2, C.1.32 and 5.2.3 producers
retain their premises; qt-d-1361-source owns final classification assembly.
This does not assert unconditional 13.2.7.

Source: Aschbacher--Smith 13.2.13, printed p.883.
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

/-- Apply 13.2.13 to the original universal terminal consumer, discharging
the entire Borel-join quotient exclusion from its earlier inputs. -/
theorem terminal_model_of_original_borel_quotient
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
    (hBaumann : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
        normalizer (ChapterB.baumann (S : Subgroup G) : Set G) ≤ normalizer (I : Set G))
    (hpairCore : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
      Context S I W W₁ W₂ W₃ →
      ∀ H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)),
        ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G) →
        Group.IsSolvable H →
        Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) →
        (H ⊔ borelResidual S I).pCoreIn 2 ≠ ⊥)
    (hsingle : ∀ (S : Sylow 2 G) (I W W₁ W₂ W₃ : Subgroup G),
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
        pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ → False)
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
  apply terminal_model_of_original_single_amalgam d hc hmany h1332 hcontexts
    rankTwo h523 hBaumann hpairCore hsingle ?_ hparameter
  intro S I W W₁ W₂ W₃ e H hH hZ hs _
  exact OriginalCentralization.not_three_borel_quotient e hH
    (hBaumann S I W W₁ W₂ W₃ e) hZ hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
