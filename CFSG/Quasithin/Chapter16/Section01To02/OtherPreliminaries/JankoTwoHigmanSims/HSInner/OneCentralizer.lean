module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure

/-!
# Odd divisors in Higman--Sims involution centralizers

The complete carrier class coverage gives either the central representative,
whose centralizer has order 7680, or the product centralizer of order 2880.
Thus every involution centralizer has order divisible by three and cannot be
a two-group. There is no ambient simplicity, Sylow or representation premise.

This intrinsic conclusion remains beside its existing class-coverage and
centralizer-structure producers to preserve the Theory/CFSG import boundary.
Source: GLS3 Table 5.3m and Aschbacher--Smith 16.1.5(10), printed p.1172.
The one-centralizer exclusion is used in Aschbacher--Smith G.4.1.
-/

public section
namespace Sporadic.LeechRelated.HS
open Subgroup
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner

/-- Every involution centralizer in the actual HS carrier has an odd prime divisor. -/
theorem three_dvd_card_involution_centralizer (i : Carrier) (hi : orderOf i = 2) :
    3 ∣ Nat.card (centralizer ({i} : Set Carrier)) := by
  rcases ClassCoverage.involution_alternative i hi with h | h
  · obtain ⟨e⟩ := ClassCoverage.centralizer_equiv_of_isConj h
    rw [Nat.card_congr e.toEquiv, centralizer_card]
    decide
  · obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, ClassCoverage.product_card]
    decide

/-- No involution in the actual HS carrier has a two-group centralizer. -/
theorem not_isPGroup_involution_centralizer (i : Carrier) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Carrier)) := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  have hd := Nat.prime_three.dvd_of_dvd_pow
    ((three_dvd_card_involution_centralizer i hi).trans hn)
  norm_num at hd

end Sporadic.LeechRelated.HS
