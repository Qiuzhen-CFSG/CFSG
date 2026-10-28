module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.ConstituentFlags
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.BoundedSplitting.SecondAction

/-!
# The exceptional four-space splitting from the earlier source theorems

The literal second-action fixed quotient supplies a central four-space
section. Its proved constituent flags establish the exact applicability of
B.4.8(4), which bounds the noncentral indecomposable constituents. Bounded
splitting then constructs a complement to all second-factor fixed vectors
inside the original V₂. The existing reconstruction transports every
B.4.8(3) clause to the resulting ambient G-submodule W₂.

The final theorem applies the actual nonsplit two-factor consumer after
discharging its fixed-supplement premise. No chief-flag, constituent bound,
complement, ambient indecomposability or offender-generation premise remains.
The genuine earlier-source inputs `EarlierB48Three` and `EarlierB48Four`
remain explicit; their producer is `qt-b-04-natural-extensions`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(3)–(4),
printed p.91, and the final B.5.6 argument, printed p.110.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
namespace ExceptionalSplitting
open ComponentReduction
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Genuine B.4.8(4), applied to the proved literal constituent flags,
constructs a complement inside the original second upper space. -/
theorem second_complement_of_fourSection
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    ∃ S : Subrepresentation (secondAmbientAction c),
      S ≤ secondUpper c ∧ IsCompl S.toSubmodule (secondAmbientAction c).invariants := by
  obtain ⟨s, hs⟩ := second_centralFourSection h483 c he f q
  have hb := smallConstituents_of_applicability h484 s s.constituentApplicability
  obtain ⟨S, hS, hc⟩ := bounded_complement s s.uniqueNoncentralNaturalFactor hb
  exact ⟨S, hs ▸ hS, hc⟩

/-- The ambient W₂ lies in literal V₂, complements C_V(G₂), and carries
the full four-dimensional source record through the original quotient map. -/
theorem ambient_splitting_of_fourSection
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    ∃ W₂ : Subrepresentation ρ,
      W₂.toSubmodule ≤ c.productConfiguration.fixed.toSubmodule ∧
      IsCompl W₂.toSubmodule (fixedSpace ρ (second c)) ∧
      Nonempty (FourDimensionalSource (W₂.toRepresentation.comp (second c).subtype)) := by
  obtain ⟨S, hS, hc⟩ := second_complement_of_fourSection h483 h484 c he f q
  exact ambient_splitting_of_complement h483 c f q S hS hc

/-- The source four-space case supplies the exact fixed-supplement equality
needed to choose the first four-space generator fixed by G₂. -/
theorem fixed_supplement_of_fourSection
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤ := by
  obtain ⟨S, hS, hc⟩ := second_complement_of_fourSection h483 h484 c he f q
  exact fixed_supplement_of_complement c S hS hc

/-- Close the exceptional second-four-space branch of B.5.6 by applying
the existing consumer with its fixed-supplement premise discharged. -/
theorem adequate_of_exceptional_fourSection
    (h483 : EarlierB48Three.{u,v}) (h484 : EarlierB48Four.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    AdequateAlternative ρ :=
  adequate_of_exceptional_fixed_supplement h483 c he f q
    (fixed_supplement_of_fourSection h483 h484 c he f q)

end ExceptionalSplitting
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
