module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankOne
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoCores
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.ParabolicInspection.Recognition.RankTwoHull

/-!
# Recognition of the actual maximal invariant parabolic

The linear and unitary rank-one branches use their Sylow-normalizer geometry.
For the rank-two families, an invariant hull covers the local intersection,
and every proper Borel overgroup has a self-centralizing two-core. Adjoining
the Sylow actor preserves characteristic two, so the supplied maximality of
the local image identifies its component intersection with the hull and
makes it maximal among proper invariant Borel overgroups.

`quotientParabolic` discharges both geometric inputs of the conditional
assembly below. The original model alternatives and both allowed central
two-covers are retained by `quotient_model`; degree-one alternatives are
excluded by `n > 1`. This proves the intermediate parabolic recognition,
before the separate residual classification and Borel equality.

Source: Aschbacher--Smith, 15.3.43, printed p.1140; 1.1.5(3)(a)--(c),
pp.501--502; A.2.3--4, p.33.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- Exhaustive assembly with the rank-two geometric inputs explicit. -/
theorem quotientParabolic_of_rankTwo_geometry
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {z : G} {n : ℕ}
    (hn : 1 < n) (hm : Model L z n)
    (hhull : ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n →
      InvariantHull (c.toComponentAction.image L) (c.toComponentAction.image S)
        (c.toComponentAction.image M))
    (hcores : ChapterA.Section02.IsTheoremCRankTwoModel (c.toComponentAction.image L) n →
      ParabolicCores (c.toComponentAction.image L) (c.toComponentAction.image S)) :
    QuotientParabolic c := by
  rcases quotient_model c hn hm with h | h | h
  · exact quotientParabolic_linear c hn h
  · exact quotientParabolic_unitary c hn h
  · exact quotientParabolic_of_geometry c (hhull h) (hcores h)

/-- The literal local component intersection in `I/C_I(L)` is a maximal
proper Sylow-invariant overgroup of the chosen Borel. Every incoming model
branch is retained, including the two permitted central covers. -/
theorem quotientParabolic_of_model
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} {n : ℕ}
    (hn : 1 < n) (hm : Model L z n) : QuotientParabolic c := by
  exact quotientParabolic_of_rankTwo_geometry c hn hm
    (rankTwo_invariantHull c hn) (rankTwo_parabolicCores c hn)

/-- The original conditional interface, retained with its exact assumptions. -/
theorem quotientParabolic
    (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    {z : G} (_hz : SourceInvolution S M z) {n : ℕ}
    (hn : 1 < n) (hm : Model L z n) : QuotientParabolic c :=
  quotientParabolic_of_model c hn hm

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.ParabolicInspection
