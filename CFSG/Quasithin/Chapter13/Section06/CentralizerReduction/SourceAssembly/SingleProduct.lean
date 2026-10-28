module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleProduct
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.PointSymmetricSeven

/-!
# The original single-factor product after every Sylow rechoice

The original Goldschmidt quotient now supplies a normal component lift
centralizing the whole omega-center, the correctly ordered dihedral and
symmetric vertices, and the literal cubic × PSL₂(p) residual with both
outer actions and an order-three lift permuting with the prescribed Sylow. The multiple-overgroup guard supplies the independent
Baumann bound at each rechoice.

Only the final cubic-product exclusion is passed to the single-factor
callback. Its original join, quotient, intersection and zero two-core
remain unchanged. The nonsolvable generation bound and genuine earlier
source inputs remain explicit; this does not assert unconditional 13.2.7
or 13.6.7. Source: Aschbacher--Smith 13.2.7, printed pp.883--884.
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

/-- The original single-factor problem is reduced, after every rechoice,
to the actual cubic × PSL₂(p) product and its centralizing component lift. -/
theorem terminal_model_of_original_single_product
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
        OriginalCentralization.SingleQuotientProduct S I H → False)
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
  obtain ⟨prod⟩ := OriginalCentralization.single_quotient_prime_product e hH hB hZ
    hSQ hg hqg hcore
  exact hproduct S I W W₁ W₂ W₃ e H hH hZ hSQ hg hqg hi hcore prod
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
