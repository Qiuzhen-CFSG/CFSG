module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.BoundedSplitting
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Consumer

/-!
# Applying bounded splitting to the original second action

The bounded-splitting theorem constructs the complement inside the literal
V₂ for the original ambient G₂-action. The published consumer then supplies
the nonsplit B.5.6 alternative. The chief flag and the constituent dimension
bound remain explicit inputs: their discharge belongs to the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the B.5.6
endgame on printed p.110, applying B.4.8(4), printed p.91.
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

/-- The bounded extraction on the original ambient second action, with
containment in the original upper space. -/
theorem second_complement_of_bounds (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f))
    (hu : UniqueNoncentralNaturalFactor (secondAmbientAction c))
    (hb : SmallNoncentralConstituents (secondAmbientAction c)) :
    ∃ S : Subrepresentation (secondAmbientAction c),
      S ≤ secondUpper c ∧ IsCompl S.toSubmodule (secondAmbientAction c).invariants := by
  obtain ⟨s,hs⟩ := second_centralFourSection h48 c he f q
  obtain ⟨S,hS,hc⟩ := bounded_complement s hu hb
  exact ⟨S,hs ▸ hS,hc⟩

/-- Actual application to the published B.5.6 consumer. Its fixed-supplement
premise is now discharged; the two constituent premises stay explicit. -/
theorem adequate_of_second_bounds (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f))
    (hu : UniqueNoncentralNaturalFactor (secondAmbientAction c))
    (hb : SmallNoncentralConstituents (secondAmbientAction c)) :
    AdequateAlternative ρ := by
  obtain ⟨S,hS,hc⟩ := second_complement_of_bounds h48 c he f q hu hb
  exact adequate_of_second_complement h48 c he f q S hS hc

end ExceptionalSplitting
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
