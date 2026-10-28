module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic

/-!
# Applying the natural-dual contradiction in the four-dimensional branch

The module classification and repeated-natural exclusion construct the
actual natural-plus-dual action from an L₄(2) quotient. Applying
`NaturalDualParabolic.false_of_source` to that action completes the
four-dimensional branch under the permitted earlier source witnesses.
Elementarity of the component span is obtained from its actual R₂ property.
No module alternative, plane marking, splitting, projected action or MS
input remains as an extra premise.

The universal B.5.1/B.4.2, I.1.6(6), and C.1.34 inputs and the exact
earlier local conclusions stay with the owning `LinearFourFive` assembly,
which must also finish the five-dimensional branch. This extension supplies
its four-dimensional contradiction without changing the sibling modules.
Both choices of Hypothesis 15.3.10 are preserved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130 (PDF pp.1146–1147).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualElimination
open RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases

universe u
variable {G : Type u} [Group G] [Finite G] (d : LocalData G)
  {I : Subgroup G} (c : ComponentWitness d I)

/-- The L₄(2) branch of 15.3.24 from the genuine earlier source results.
`FourModules.naturalDual_plane_split` supplies the actual module to the
natural-dual exclusion; the earlier R₂ conclusion supplies elementarity.
The universal classification and cohomology witnesses and the explicit
15.3.2–17 clauses remain obligations of the parent source assembly. -/
theorem exclusion_of_earlier
    (ffClassification : Sieve.UniversalFFClassification.{u,u})
    (cohomology : Sieve.UniversalNaturalCohomology)
    (msClassification : UniversalClassification.{u})
    (hI : I ∈ d.Hplus) (hf : CharacteristicTwo.HasCharacteristicTwo I)
    (hrank : primeRank 3 d.Yplus = 2) (earlier : Preparation.Earlier d c)
    (hq : IsSQTK KnownSimple.IsKnownSimple I)
    (model : (c.L ⧸ pCore 2 c.L) ≃* Projective 4)
    (hW : d.componentSpan c.L ≤ c.L ⊔ d.R)
    (hred : IsR2Within (d.componentSpan c.L) (c.L ⊔ d.R))
    (hLRcore : (c.L ⊔ d.R).pCoreIn 2 ≤ d.R)
    (hJ : c.L = ⁅c.L, Stellmacher.elementaryAbelianMaxJ d.R⁆)
    (hR : d.R ≤ centralizer (d.V : Set G))
    (hC : centralizer (d.V : Set G) ≤ d.M)
    (hMc : d.Mc = centralizer (d.Z : Set G))
    (hinter : d.M ⊓ d.Mc =
      (d.M ⊓ centralizer (d.V : Set G)) ⊔ (d.T : Subgroup G))
    (h7image : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (h7span : localSpan d.Z d.Y = d.V)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (hnormalizer : OutsideStructure.SecondChoice d → normalizer (d.V₁ : Set G) ≤ d.M)
    (h11 : ∀ J : Subgroup G, J ≤ I →
      ⁅d.V, Stellmacher.twoResidualAmbient (d.Y ⊓ J)⁆ ≠ ⊥ → ¬ J ≤ d.M →
      ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
        ¬ ((C.map d.S.subtype).subgroupOf (J ⊔ d.S)).Normal)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) : False := by
  obtain ⟨h, _, _⟩ := FourModules.naturalDual_plane_split d c ffClassification cohomology
    hI hf hrank earlier hq model hW hred hLRcore hJ hR hC hMc hinter h7image h7span h7
  let _ := hred.elementary
  let _ : IsElementaryAbelian 2 (d.componentSpan c.L) :=
    IsElementaryAbelian.of_surjective (subgroupOfEquivOfLe hW).toMonoidHom
      (subgroupOfEquivOfLe hW).surjective
  exact NaturalDualParabolic.false_of_source c msClassification hI hf hrank earlier hq h
    hR h7span hnormalizer h11 hindex hZ hZS

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualElimination

end
