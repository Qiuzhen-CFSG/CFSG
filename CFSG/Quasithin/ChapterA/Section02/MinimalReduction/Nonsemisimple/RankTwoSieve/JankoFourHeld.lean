module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankReduction
public import Theory.SpecificGroups.Janko4.TwoRankLower
public import Theory.SpecificGroups.Held.TwoRankLower
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.TwoRankLower
public import Theory.SpecificGroups.Rudvalis.TwoRankLower

/-!
# Four further sporadic entries in the source two-rank sieve

The certified local elementary subgroups of orders 2048, 64, eight and eight
exclude J₄, Held, Higman–Sims and Rudvalis on their literal carriers. The source application transports the bounds
to the actual quotient S/Z(S).
Source: Aschbacher–Smith A.2.12, printed p.36.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
/-- The two specified sporadic entries have two-rank greater than two. -/
theorem no_janko_four_held_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (name : KnownSimple.SporadicName)
    (hname : name = .j4 ∨ name = .he) (a : Q ≃* name.Carrier) : False := by
  have hb : 3 ≤ primeRank 2 name.Carrier := by
    rcases hname with rfl | rfl
    · exact (by decide : 3 ≤ 11).trans Janko4.eleven_le_twoRank
    · exact (by decide : 3 ≤ 6).trans Held.six_le_twoRank
  let : Finite name.Carrier := Finite.of_equiv Q a.toEquiv
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
/-- The two marked eight-subgroups exclude the Higman–Sims and Rudvalis entries. -/
theorem no_higman_sims_rudvalis_model {Q : Type u} [Group Q] [Finite Q]
    (hr : primeRank 2 Q ≤ 2) (name : KnownSimple.SporadicName)
    (hname : name = .hs ∨ name = .ru) (a : Q ≃* name.Carrier) : False := by
  have hb : 3 ≤ primeRank 2 name.Carrier := by
    rcases hname with rfl | rfl
    · exact Sporadic.LeechRelated.HS.three_le_twoRank
    · exact Rudvalis.three_le_twoRank
  let : Finite name.Carrier := Finite.of_equiv Q a.toEquiv
  rw [← Theory.GroupTheory.primeRank_equiv 2 a] at hb
  omega
end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}
/-- The actual source quotient is neither J₄ nor Held. -/
theorem CounterexampleToTheoremA.centralQuotient_no_janko_four_held_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (name : KnownSimple.SporadicName)
    (hname : name = .j4 ∨ name = .he) (a : (S ⧸ center S) ≃* name.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_janko_four_held_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) name hname a
/-- The actual source quotient is neither Higman–Sims nor Rudvalis. -/
theorem CounterexampleToTheoremA.centralQuotient_no_higman_sims_rudvalis_model
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (hn : ¬ IsSemisimple G) (name : KnownSimple.SporadicName)
    (hname : name = .hs ∨ name = .ru) (a : (S ⧸ center S) ≃* name.Carrier) : False :=
  Nonsemisimple.RankTwoSieve.no_higman_sims_rudvalis_model
    (h.section_centralQuotient_twoRank_le_two_of_not_semisimple ih hn) name hname a
end CFSG.Quasithin.ChapterA.Section02
