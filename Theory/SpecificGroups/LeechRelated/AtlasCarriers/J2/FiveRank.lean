module
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddLocal.Five
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The five-rank of the concrete Hall–Janko group

The existing checked odd-local words generate a subgroup of order25.
Their commutation and fifth-power identities make that subgroup elementary
abelian, giving the lower bound two for the five-rank. No new finite
enumeration is required.

Source: the ATLAS J₂ degree100 model and its marked odd-local calculation
in `J2UpperBound.OddLocal.Five`; application to Aschbacher–Smith13.6.27,
printed p.934, excludes a commuting Suzuki component in an SQTK group.
-/

public section
namespace Sporadic.LeechRelated.J2
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.J2HSMultipliers.J2.UpperBound.OddLocal.Five

/-- The native J₂ carrier contains an elementary abelian subgroup of order25. -/
theorem five_rank_ge_two : 2 ≤ primeRank 5 Carrier := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsMulCommutative (closure ({x,y} : Set Carrier)) := isMulCommutative_closure (by
    rintro _ (rfl | rfl) _ (rfl | rfl)
    · rfl
    · exact x_commute_y.eq
    · exact x_commute_y.symm.eq
    · rfl)
  let : IsElementaryAbelian 5 P := IsElementaryAbelian.closure_of_isMulCommutative
    ({x,y} : Set Carrier) (by rintro _ (rfl | rfl); exact x_pow; exact y_pow)
  exact IsElementaryAbelian.primeRank_ge_of_card (p := 5) (n := 2) P
    (by norm_num [card_P])

end Sporadic.LeechRelated.J2
