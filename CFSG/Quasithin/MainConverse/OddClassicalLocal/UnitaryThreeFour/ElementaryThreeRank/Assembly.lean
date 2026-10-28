module

public import CFSG.Quasithin.MainConverse.OddClassicalLocal.UnitaryThreeFour.ElementaryThreeRank
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.InvolutionCentralizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.TraceBound

/-!
# PSU₄(3): elementary normalizer three-ranks and quasithinness

Every lift of a nonidentity projective involution has trace zero. This
discharges the trace premise in the elementary size and centralizer
calculations: an elementary two-subgroup has order at most sixteen, and
centralizers in orders two, four and sixteen have orders indivisible by
27, 9 and 3, respectively. The order-eight case follows from a four-subgroup.
The actual conjugation action on each elementary subgroup then bounds its
normalizer's three-rank by two.

The elementary-normalizer reduction and the already proved nondefining-prime
bounds give quasithinness of the concrete PSU₄(3) image over `FiniteField.Nine`.
All model premises are discharged; the full scalar kernel and ambient
projective normalizers are retained throughout.

This proves the QT clause for PSU₄(3) in Aschbacher–Smith, Theorem 0.1.2(4),
printed p.4 of `refs/quasithin.pdf`, restated as Theorem 0.1.1(4), printed
p.482. The SU-to-PSU convention is that of GLS3, chapter 2, §2.7.
-/

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal

namespace CFSG.Quasithin.MainConverse.UnitaryFourThree

/-- Every nonidentity elementary two-subgroup in a Sylow two-subgroup of the
actual PSU₄(3) model has an ambient normalizer of three-rank at most two. -/
public theorem elementary_normalizer_three_rank
    (S : Sylow 2 (Carrier 4))
    (A : Subgroup (Carrier 4)) (hAS : A ≤ (S : Subgroup (Carrier 4)))
    (hA : A ≠ ⊥) (hEA : IsElementaryAbelian 2 A) :
    primeRank 3 (Subgroup.normalizer (A : Set (Carrier 4))) ≤ 2 := by
  have htrace := InvolutionCentralizer.trace_eq_zero_of_projective_involution
  exact elementary_normalizer_three_rank_of_centralizer_bounds S
    (fun B _ hB => elementary_card_le_sixteen htrace B hB)
    (fun B _ _ hB => InvolutionCentralizer.centralizer_three_part_of_card_eq_two B hB)
    (fun B _ hB hcard => FourCentralizer.four_centralizer_not_nine_dvd_of_trace
      htrace B hB hcard)
    (fun B _ hB hcard => centralizer_not_three_dvd_of_card_eq_sixteen
      htrace B hB hcard)
    A hAS hA hEA

/-- The concrete projective special-unitary group PSU₄(3) is quasithin. -/
public theorem model_quasithin : IsQuasithin (Carrier 4) := by
  let S : Sylow 2 (Carrier 4) := Classical.choice inferInstance
  exact model_quasithin_of_elementary_normalizer_rank S
    (elementary_normalizer_three_rank S)

end CFSG.Quasithin.MainConverse.UnitaryFourThree
