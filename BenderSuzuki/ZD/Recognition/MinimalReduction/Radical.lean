module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.OddQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralQuotient

/-!
# Solvable-normal reduction for a minimal ZD counterexample

The elementary reduction, fusion transporters, odd and central quotient
product-disconnection descent, and the structural central-quotient induction
step are proved in the imported modules. The final conditional reduction
below uses Fitting theory to reduce all solvable normal subgroups to the
odd core and central subgroups of order two.

To complete GLS, Volume 4, Chapter 2, Lemma 4.5 (printed pp. 34–35), one
must still establish odd-core containment using Lemma 3.13 and lift the full
ZD conclusion through the odd-core and central order-two quotients. These
remaining source arguments are not hypotheses of an asserted source theorem.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G}

/-- Conditional final reduction: trivial odd core and exclusion of central
subgroups of order two eliminate every solvable normal subgroup. The quotient
lifting arguments must establish these two premises in the minimal case. -/
public theorem solvable_normal_eq_bot_of_core_and_central_exclusion
    (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hodd : pPrimeCore 2 G = ⊥)
    (hexclude : ∀ A : Subgroup G, A.Normal → A ≤ Subgroup.center G → Nat.card A ≠ 2)
    (N : Subgroup G) (hN : N.Normal) (hsol : Group.IsSolvable N) : N = ⊥ := by
  let : N.Normal := hN
  let : Group.IsSolvable N := hsol
  by_contra hne
  obtain ⟨A, hAn, _, hAc, hcard⟩ := central_two_subgroup_of_solvable_normal
    hgen hcentral hodd N hne
  exact hexclude A hAn hAc hcard

end BenderSuzuki.ZD
