module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.Covers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.Cohomology

/-!
# Applying the proved I.1 inputs to the degree-eight consumer

The universal A₈ cover-kernel bound and dual natural H¹ vanishing discharge
both I.1 premises of `NaturalModule.natural_module_of_source`. The resulting
action is still marked by the original star projection, and the conclusion
retains both core-centralizer identities and the two fixed-plane identities.

The actual component, its supplied S₈ marking, the earlier local conclusions,
B.4/B.5 classification and B.2.14 splitting remain explicit source inputs.
The full rank-one branch and Theorem 15.3.25 are not concluded here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the paragraph preceding 15.3.32 and 15.3.32(1),(2), printed pp.1132–1133;
I.1.3 and I.1.5–6, printed pp.407–408.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.DegreeEight
open RankOneConfiguration.EightGeometry.NaturalModule
universe u
variable {G : Type u} [Group G] [Finite G]
  (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
  (hnormal : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
  (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
  (e : d.Star I ≃* Equiv.Perm (Fin 8))
  (hmark : (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8))

include hnormal hI P hP hmark in
/-- The marked degree-eight action and fixed geometry with both I.1 inputs proved. -/
theorem natural_module_of_source
    (classification : Recognition.FFSpecialization.Sieve.UniversalFFClassification.{u,u})
    (splitting : FixedGeometry.SourceB214Splitting.{u})
    (hchar : HasCharacteristicTwo I)
    (hSQTK : IsSQTK KnownSimple.IsKnownSimple (d.starImage I c.L))
    (hYL : d.Yplus ≤ c.L)
    (hRank : primeRank 3 d.Yplus = 1) (hYRank : 2 ≤ primeRank 3 d.Y)
    (htheta : theta (d.MI I) = d.Yplus)
    (hnorm : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hplane : ⁅d.V, d.Yplus⁆ = d.V₂)
    (hfull : ⁅d.V₂, d.Yplus⁆ = d.V₂)
    (hseed : d.V₂ ≤ localSpan d.Z d.Yplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (hOmega : d.ZS = Stellmacher.omegaOneCenterAmbient d.S)
    (mark : Recognition.Models.MiddleNodeMarking
      (d.starImage I c.L) (d.starImage I (d.M ⊓ c.L))) :
    ∃ a : NaturalEightAction I (d.componentModule I c.L),
      a.actor = e.toMonoidHom.comp (d.starMap I) ∧
      I.pCoreIn 2 = I ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      I.pCoreIn 2 = d.S ⊓ centralizer (d.componentModule I c.L : Set G) ∧
      d.ZS ⊓ centralizer (c.L : Set G) = d.ZS ⊓ d.V₁ ∧
      Nat.card (d.ZS ⊓ d.V₁ : Subgroup G) = 2 ∧
      d.ZS ⊓ d.componentModule I c.L = d.ZS ⊓ d.V₂ := by
  exact RankOneConfiguration.EightGeometry.NaturalModule.natural_module_of_source
    d c hnormal hI P hP e hmark eightCoverKernelTwo classification
    universalNaturalCohomology splitting hchar hSQTK hYL hRank hYRank htheta hnorm
    hplane hfull hseed hindex hZ hZS hOmega mark

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceInputs.DegreeEight

end
