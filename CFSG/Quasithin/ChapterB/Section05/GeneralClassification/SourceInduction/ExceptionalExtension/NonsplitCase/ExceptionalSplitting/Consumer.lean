module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase

/-!
# Application to the published nonsplit two-factor assembly

The literal second-action complement discharges the fixed-supplement premise
of the existing B.5.6 assembly. This application retains the full earlier
B.4.8(3) input and both four-dimensional source records. Existence of the
complement remains with the constituent and bounded-splitting proofs; no
completion of the nonsplit source branch is claimed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6 endgame,
printed p.110, applying B.4.8(3)–(4), printed p.91.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
namespace ExceptionalSplitting
open ComponentReduction
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The exact existing consumer, applied to the complement's supplement. -/
theorem adequate_of_second_complement (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (he : IsExceptional ρ c.first c.sectionData.space)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f))
    (S : Subrepresentation (secondAmbientAction c)) (hS : S ≤ secondUpper c)
    (hc : IsCompl S.toSubmodule (secondAmbientAction c).invariants) :
    AdequateAlternative ρ :=
  adequate_of_exceptional_fixed_supplement h48 c he f q
    (fixed_supplement_of_complement c S hS hc)

end ExceptionalSplitting
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
