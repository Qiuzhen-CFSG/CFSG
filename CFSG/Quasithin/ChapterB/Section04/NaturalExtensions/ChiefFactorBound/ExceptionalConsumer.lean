module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.ChiefFactorBound
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Source

/-!
# Discharging the chief-factor bound in the B.5 exceptional branch

The proved B.4.8(4) implication is supplied to the actual second-factor
splitting argument, with its original actions, subspaces and quotient maps.
This removes `EarlierB48Four` from both the complement construction and the
resulting adequate alternative. The independent full B.4.8(3) input remains
with its source owner, `qt-b-04-natural-extensions`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(3)–(4),
printed p.91, and the nonsplit B.5.6 endgame, printed p.110.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension
open CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open ExceptionalSplitting ComponentReduction

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.ChiefFactorBound
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- B.4.8(4) supplies the bound needed for the actual second-factor complement. -/
theorem exceptional_second_complement
    (h483 : EarlierB48Three.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    ∃ S : Subrepresentation (secondAmbientAction c),
      S ≤ secondUpper c ∧ IsCompl S.toSubmodule (secondAmbientAction c).invariants :=
  second_complement_of_fourSection h483 earlierB48Four c he f q

/-- The literal B.5.6 exceptional branch, with its B.4.8(4) premise discharged. -/
theorem exceptional_adequate_alternative
    (h483 : EarlierB48Three.{u,v})
    (c : Conclusion ρ) (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f)) :
    AdequateAlternative ρ :=
  adequate_of_exceptional_fourSection h483 earlierB48Four c he f q

end CFSG.Quasithin.ChapterB.NaturalExtensions.ChiefFactorBound
