module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.Cohomology

/-!
# Applying I.1.6(6) to the conditional 15.3.24 exclusion

This application discharges the dual natural H¹ input of
`LinearFourFive.Source.not_four_and_not_five_of_earlier` using the actual
four- and five-dimensional projective actions. Both binary exclusions
retain their original component witnesses and core quotients.

The B.4/B.5 and C.1.34 classification witnesses, genuine earlier local
conclusions, and smaller-overgroup component/model/L₃ inputs remain explicit.
Their producers and full 15.3.13/25 assembly remain with the existing source
owners. This theorem does not assert the characteristic-two exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130, and I.1.6(6), printed p.408.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.LinearFourFive
open RankTwoElimination RankTwoElimination.LinearFourFive RankTwoElimination.LinearFourFive.Source
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u
variable {G : Type u} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}

/-- The conditional L₄/L₅ exclusion with the cohomological premise proved. -/
theorem not_four_and_not_five_of_earlier
    (ffClassification : Sieve.UniversalFFClassification.{u,u})
    (msClassification : UniversalClassification.{u})
    (ambient : AmbientConclusions d)
    (hI : I ∈ d.Hplus) (hf : HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2)
    (hq : IsSQTK KnownSimple.IsKnownSimple I)
    (hcontrol : SolvableInvariantControl d I)
    (h11 : ∀ K : Subgroup G, K ≤ I → K ∈ d.Hplus →
      OutsideStructure.Conclusions d K)
    (hcomponent : ∀ (K : Subgroup G), K ≤ I → K ∈ d.Hplus →
      HasCharacteristicTwo K → ∀ cK : ComponentWitness d K,
      ∀ n : ℕ, (n = 4 ∨ n = 5) →
      Nonempty ((cK.L ⧸ pCore 2 cK.L) ≃* Projective n) → ComponentConclusions d cK)
    (components : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      Nonempty (ComponentWitness d K))
    (binary_models : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      ∀ cK : ComponentWitness d K, ∃ n, (n = 3 ∨ n = 4 ∨ n = 5) ∧
        Nonempty ((cK.L ⧸ pCore 2 cK.L) ≃* Projective n))
    (no_three : ∀ K : Subgroup G, K < I → K ∈ d.Hplus →
      HasCharacteristicTwo K → Chapter1.IsSylowIn 2 d.S K →
      SolvableInvariantControl d K → primeRank 3 d.Yplus = 2 →
      ∀ cK : ComponentWitness d K,
        ((cK.L ⧸ pCore 2 cK.L) ≃* Projective 3) → False)
    (c : ComponentWitness d I) :
    (¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 4)) ∧
      ¬ Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Projective 5) := by
  exact RankTwoElimination.LinearFourFive.Source.not_four_and_not_five_of_earlier
    ffClassification universalNaturalCohomology msClassification ambient hI hf hrank hq
    hcontrol h11 hcomponent components binary_models no_three c

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.LinearFourFive

end
