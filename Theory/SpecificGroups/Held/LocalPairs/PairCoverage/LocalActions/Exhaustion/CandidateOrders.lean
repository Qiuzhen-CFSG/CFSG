module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Support
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Local0
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Pair00Words
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.JoinBounds

/-!
# Assembling literal Held candidate orders from independent bounds

The two factor orders are coprime. Lagrange therefore forces their product
to divide the order of their actual join. A separate upper bound for that
join supplies equality. Thus the factor-order and join-bound certificates
can be developed independently, without normalizer or plane calculations.

The kernel-checked factor and join certificates discharge both premises,
giving the unconditional `candidateOrders` theorem for all four literal pairs.
Source: the literal words in LocalActions/Candidates and the exploration
in LocalActions/source; GLS3 Table 5.3p and quasithin printed pp.509–511.
-/

namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
open Subgroup

/-- Complementary certified factor orders and a bound determine the actual join order. -/
public theorem candidateProduct_card_of_factorOrders_of_joinBound
    (i : Bool) (j : Fin 2)
    (htwo : Nat.card (candidateTwo i j) = 1024)
    (hodd : Nat.card (candidateOdd i j) = 9)
    (hupper : Nat.card (candidateProduct i j) ≤ 9216) :
    Nat.card (candidateProduct i j) = 9216 := by
  apply Nat.le_antisymm hupper
  have ht : 1024 ∣ Nat.card (candidateProduct i j) := by
    rw [← htwo]
    exact card_dvd_of_le (show candidateTwo i j ≤ candidateProduct i j from le_sup_right)
  have hr : 9 ∣ Nat.card (candidateProduct i j) := by
    rw [← hodd]
    exact card_dvd_of_le (show candidateOdd i j ≤ candidateProduct i j from le_sup_left)
  exact Nat.le_of_dvd Nat.card_pos
    ((by decide : Nat.Coprime 1024 9).mul_dvd_of_dvd_of_dvd ht hr)

/-- Final order assembly; both independent concrete certificate families are required. -/
public theorem candidateOrders_of_factorOrders_of_joinBound
    (hf : ∀ (i : Bool) (j : Fin 2),
      Nat.card (candidateTwo i j) = 1024 ∧ Nat.card (candidateOdd i j) = 9)
    (hj : ∀ (i : Bool) (j : Fin 2), Nat.card (candidateProduct i j) ≤ 9216) :
    CandidateOrders := by
  intro i j
  exact ⟨(hf i j).1, (hf i j).2,
    candidateProduct_card_of_factorOrders_of_joinBound i j (hf i j).1 (hf i j).2 (hj i j)⟩

/-- Every literal candidate pair has factor orders 1024 and 9 and actual join order 9216. -/
public theorem candidateOrders : CandidateOrders :=
  candidateOrders_of_factorOrders_of_joinBound candidateFactorOrders candidateProduct_card_le_9216

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
