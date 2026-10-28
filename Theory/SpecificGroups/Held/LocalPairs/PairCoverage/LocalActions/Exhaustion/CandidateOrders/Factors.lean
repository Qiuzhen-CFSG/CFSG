module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.Contracts
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Candidates
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Two
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair00Odd
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair01Odd
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair10Odd
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair11Odd
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair01Conjugacy
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair10Conjugacy
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalActions.Exhaustion.CandidateOrders.Factors.Pair11Conjugacy
import Mathlib.Tactic.FinCases

/-!
# Exact orders of the literal Held candidate factors

The order-nine factors and the first order-1024 factor are counted by a
certified cyclic series and a decoder distinguishing their normal forms.
Explicit permutation conjugators transfer the latter count to the other
three literal two-subgroups. Every relation is checked in the unchanged
ATLAS action; no Held order, recognition, or simplicity result is used.
Sources: ATLAS HeG1-p2058B0 and max3/max4; LocalActions/source/Explore.g;
proposed words and reproducible certificates in CandidateOrders/source and
CandidateOrders/Factors/source.
-/

public section
namespace Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
open CandidateOrderCertificate
open CandidateOrderCertificate.Factors

private theorem two_card_table (i : Bool) (j : Fin 2)
    (f : Fin 4 → Equiv.Perm (Fin 2058))
    (hf : ∀ k, f k = representation (evalLocalWord i (twoWord i j k))) :
    Nat.card (candidateTwo i j) = Nat.card (Subgroup.closure (Set.range f)) := by
  have h := card_closure_image representation representation_injective
    (fun k => evalLocalWord i (twoWord i j k))
  simpa only [candidateTwo, ← hf] using h

private theorem odd_order_00 : Nat.card (candidateOdd false 0) = 9 := by
  have he : (fun k => evalLocalWord false (oddWord false 0 k)) = Pair00Odd.input := by
    funext k
    fin_cases k <;> rfl
  simpa only [candidateOdd, he] using Pair00Odd.order

private theorem odd_order_01 : Nat.card (candidateOdd false 1) = 9 := by
  have he : (fun k => evalLocalWord false (oddWord false 1 k)) = Pair01Odd.input := by
    funext k
    fin_cases k <;> rfl
  simpa only [candidateOdd, he] using Pair01Odd.order

private theorem odd_order_10 : Nat.card (candidateOdd true 0) = 9 := by
  have he : (fun k => evalLocalWord true (oddWord true 0 k)) = Pair10Odd.input := by
    funext k
    fin_cases k <;> rfl
  simpa only [candidateOdd, he] using Pair10Odd.order

private theorem odd_order_11 : Nat.card (candidateOdd true 1) = 9 := by
  have he : (fun k => evalLocalWord true (oddWord true 1 k)) = Pair11Odd.input := by
    funext k
    fin_cases k <;> rfl
  simpa only [candidateOdd, he] using Pair11Odd.order

private theorem two_order_00 : Nat.card (candidateTwo false 0) = 1024 := by
  have he : (fun k => evalLocalWord false (twoWord false 0 k)) = Pair00Two.input := by
    funext k
    fin_cases k <;> rfl
  simpa only [candidateTwo, he] using Pair00Two.order

private theorem two_order_01 : Nat.card (candidateTwo false 1) = 1024 := by
  have hs := two_card_table false 0 Pair01Conjugacy.sourceGenerator (by
    intro k
    fin_cases k <;> exact Pair00.generatorTable_eq _)
  have ht := two_card_table false 1 Pair01Conjugacy.targetGenerator (by
    intro k
    fin_cases k <;> exact Pair01.generatorTable_eq _)
  rw [ht, ← Pair01Conjugacy.card_eq, ← hs, two_order_00]

private theorem two_order_10 : Nat.card (candidateTwo true 0) = 1024 := by
  have hs := two_card_table false 0 Pair10Conjugacy.sourceGenerator (by
    intro k
    fin_cases k <;> exact Pair00.generatorTable_eq _)
  have ht := two_card_table true 0 Pair10Conjugacy.targetGenerator (by
    intro k
    fin_cases k <;> exact Pair10.generatorTable_eq _)
  rw [ht, ← Pair10Conjugacy.card_eq, ← hs, two_order_00]

private theorem two_order_11 : Nat.card (candidateTwo true 1) = 1024 := by
  have hs := two_card_table false 0 Pair11Conjugacy.sourceGenerator (by
    intro k
    fin_cases k <;> exact Pair00.generatorTable_eq _)
  have ht := two_card_table true 1 Pair11Conjugacy.targetGenerator (by
    intro k
    fin_cases k <;> exact Pair11.generatorTable_eq _)
  rw [ht, ← Pair11Conjugacy.card_eq, ← hs, two_order_00]

/-- The unchanged literal two- and odd-factor closures have orders 1024 and 9. -/
theorem candidateFactorOrders (i : Bool) (j : Fin 2) :
    Nat.card (candidateTwo i j) = 1024 ∧ Nat.card (candidateOdd i j) = 9 := by
  cases i <;> fin_cases j
  · exact ⟨two_order_00, odd_order_00⟩
  · exact ⟨two_order_01, odd_order_01⟩
  · exact ⟨two_order_10, odd_order_10⟩
  · exact ⟨two_order_11, odd_order_11⟩

end Held.LocalPairs.PairCoverage.LocalActions.Exhaustion
