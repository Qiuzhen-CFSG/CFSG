module

public import CFSG.KnownSimple.ClassicalModels
public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.SpecificGroups.PSL2.OddTwoLocalRank

/-!
# The actual PSL₂ local-rank bound in the source rank-two sieve

The model inequality is transported through the supplied multiplicative
equivalence. Its source application uses exactly S/Z(S), the original
counterexample's odd prime, and no quasithinness premise for a quotient.
The earlier source owner separately transports this rank through the
actual central cover S→S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- Every odd-field PSL₂ model has odd-prime two-local rank at most two. -/
theorem odd_psl_two_twoLocalRank_le_two {Q : Type u} [Group Q] [Finite Q]
    {p q : ℕ} (hp : p.Prime) (ho : Odd p) (hq : GorensteinWalter.IsOddPrimePower q)
    (model : ClassicalGroup.IsPSL Q 2 q) : twoLocalPrimeRank p Q ≤ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := model
  rw [twoLocalPrimeRank_mulEquiv p a]
  exact Theory.PSL2.odd_twoLocalPrimeRank_le_two (by simpa only [hcard] using hq) ho
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual central quotient has the required local bound whenever it is an odd-field PSL₂. -/
theorem CounterexampleToTheoremA.centralQuotient_odd_psl_two_localRank_le_two
    (h : CounterexampleToTheoremA K G S p) {q : ℕ}
    (hq : GorensteinWalter.IsOddPrimePower q)
    (model : ClassicalGroup.IsPSL (S ⧸ center S) 2 q) :
    twoLocalPrimeRank p (S ⧸ center S) ≤ 2 :=
  Nonsemisimple.RankTwoSieve.odd_psl_two_twoLocalRank_le_two
    h.2.2.2.2.1 h.2.2.2.2.2.1 hq model
end CFSG.Quasithin.ChapterA.Section02
