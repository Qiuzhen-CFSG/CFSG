module

public import Theory.SpecificGroups.BabyMonster.Order.Bounds
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup

/-!
# A centralizer-quotient route to the Baby Monster upper bound

The structural route to the `Y₄₃₃` presentation identifies it with the quotient
of a Monster 2A-involution centralizer by its distinguished involution.
An injection into that quotient is already sufficient for the upper bound.
Lagrange's theorem divides the centralizer bound by two, and the injection
transfers both finiteness and the bound to the fixed presented carrier.

This is only the final counting step. Neither the injection nor the concrete
centralizer bound is assumed to have been constructed. The presentation route
is described in Breuer–Magaard–Wilson (2019), §§2–3.1,
https://arxiv.org/abs/1902.07758, citing Ivanov, *Presenting the Baby Monster*,
J. Algebra 163 (1994), 88–108, and Griess's Monster multiplier calculation.
-/

public section

namespace BabyMonster.OrderUpperBound

/-- A faithful map into a finite quotient of a group of at most twice the
target order suffices when the subgroup being factored out has order two.
Only the underlying coset set is needed for this cardinality argument. -/
theorem finite_and_card_le_of_quotient_injection
    {E : Type*} [Group E] [Finite E] (Z : Subgroup E)
    (f : Carrier → E ⧸ Z) (hf : Function.Injective f)
    (hZ : Nat.card Z = 2) (hE : Nat.card E ≤ 2 * expectedOrder) :
    Finite Carrier ∧ Nat.card Carrier ≤ expectedOrder := by
  have hquot : Nat.card (E ⧸ Z) ≤ expectedOrder := by
    rw [Z.card_eq_card_quotient_mul_card_subgroup, hZ, Nat.mul_comm] at hE
    exact Nat.le_of_mul_le_mul_left hE (by decide : 0 < 2)
  exact ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans hquot⟩

/-- In particular, the structural route needs a faithful map to the quotient
of an involution centralizer, and an upper bound for that actual centralizer.
No finiteness assumption on the presented Baby Monster is used. -/
theorem finite_and_card_le_of_involution_centralizer
    {M : Type*} [Group M] (z : M)
    [Finite (Subgroup.centralizer ({z} : Set M))]
    (hz : orderOf z = 2)
    (f : Carrier → (Subgroup.centralizer ({z} : Set M)) ⧸
      (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set M)))
    (hf : Function.Injective f)
    (hC : Nat.card (Subgroup.centralizer ({z} : Set M)) ≤ 2 * expectedOrder) :
    Finite Carrier ∧ Nat.card Carrier ≤ expectedOrder := by
  have hzC : Subgroup.zpowers z ≤ Subgroup.centralizer ({z} : Set M) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z))
  apply finite_and_card_le_of_quotient_injection _ f hf _ hC
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzC).toEquiv,
    Nat.card_zpowers, hz]

end BabyMonster.OrderUpperBound
