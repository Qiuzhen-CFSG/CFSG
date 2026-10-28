module
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore
public import Theory.SpecificGroups.ONan.OddCentralLocalRank

/-!
# The original O'Nan odd-cover source branch

The original counterexample and proper-section induction give odd center.
The literal O'Nan normalizer words then construct commuting cubic lifts and
a genuine two-local subgroup of three-rank at least three, contradicting the
original ambient quasithinness. No universal-cover lift or center-order bound
is taken as an input.

This closes the O'Nan Case II leaf of Aschbacher–Smith A.2.19, printed p.41,
for the actual 45-dimensional projective matrix carrier used by the catalogue.
-/
namespace CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore
universe u
open Subgroup Theory.GroupTheory
variable {G S : Type u} [Group G] [Finite G] [Group S] [Finite S]
  [IsQuasisimple G] {p : ℕ}

/-- The original hypotheses exclude the actual O'Nan central quotient.
The proof constructs the needed local lifts from concrete inverter words. -/
public theorem cover_onan_of_local_inversion
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (e : G ⧸ center G ≃* ONan.Model) : False :=
  ONan.OddCentralLocalRank.not_quasithin (center_odd_card h ih) e h.1

end CFSG.Quasithin.ChapterA.Section02.Sporadic.SourceAssembly.WithoutPrimeCore
