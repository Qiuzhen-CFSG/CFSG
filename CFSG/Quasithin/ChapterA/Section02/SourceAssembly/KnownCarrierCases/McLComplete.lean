module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.KnownCarrierCases
/-!
# Discharging the McLaughlin premise in the original A.2 source cases

The actual permutation-to-Leech comparison supplies the last McLaughlin model
premise. The remaining explicit source producers are the Fi24 involution-
centralizer section and the O'Nan compatible central-cover lift.
Source: Aschbacher--Smith A.2.19, printed pp.40--41.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- Original quasisimple source exclusion with the McLaughlin comparison discharged. -/
theorem CounterexampleToTheoremA.quasisimple_false_of_fi24_onan [IsQuasisimple G]
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G,
        (Sporadic.SourceAssembly.projection e).comp F = ONan.Cover.projection) : False :=
  h.quasisimple_false_of_fi24_mcl_onan ih
    Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv d24 hlift
/-- The same exact source producer closes every semisimple counterexample. -/
theorem CounterexampleToTheoremA.semisimple_false_of_fi24_onan
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G) (hsemi : IsSemisimple G)
    (d24 : InvolutionCentralizerQuotientData _root_.Sporadic.Fischer.Fi24Prime.Carrier
      _root_.Sporadic.Fischer.Fi22.Carrier)
    (hlift : ∀ e : G ⧸ center G ≃* ONan.Model,
      ∃ F : ONan.Cover.linearSubgroup →* G,
        (Sporadic.SourceAssembly.projection e).comp F = ONan.Cover.projection) : False :=
  h.semisimple_false_of_fi24_mcl_onan ih hsemi
    Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv d24 hlift
end CFSG.Quasithin.ChapterA.Section02
