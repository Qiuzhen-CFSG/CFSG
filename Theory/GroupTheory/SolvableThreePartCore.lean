module

public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.SelfCentralizingCore
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Two-cores with a three-part of order at most three

A solvable {2,3}-group with three-core of order at most three and order
divisible by four has nontrivial two-core. Otherwise its Fitting subgroup
is cyclic of order one or three and self-centralizing, so conjugation
bounds the two-part of the whole group by two.

We also record the normal-subgroup step needed after parabolic placement:
a nontrivial solvable normal subgroup of a group of characteristic p has
nontrivial p-core. This retains normality in the containing group.

Source: the elementary Fitting argument in Aschbacher–Smith, proof of
Proposition 1.3.4, printed p.511, used in 15.3.28, printed p.1131.
-/

public section
open Subgroup
namespace Theory.GroupTheory

/-- The small three-part version works already with a two-part of order four. -/
theorem twoCore_ne_bot_of_solvable_threeCore_le_three
    {G : Type*} [Group G] [Finite G] (hs : Group.IsSolvable G)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card G → p = 2 ∨ p = 3)
    (hsmall : Nat.card (pCore 3 G) ≤ 3) (hfour : 4 ∣ Nat.card G) :
    pCore 2 G ≠ ⊥ := by
  intro htwo
  have hfit : fittingSubgroup G = pCore 3 G := by
    apply le_antisymm _ (pCore_le_fitting G 3)
    rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    rcases hprime p.val.val (Nat.prime_of_mem_primeFactors p.val.property)
      (Nat.dvd_of_mem_primeFactors p.val.property) with he | he
    · rw [he, htwo]
      exact bot_le
    · rw [he]
  have hcentral : centralizer (pCore 3 G : Set G) ≤ pCore 3 G := by
    rw [← hfit]
    exact centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs
  let N := pCore 3 G
  have hcases : Nat.card N = 1 ∨ Nat.card N = 3 := by
    rcases (pCore_isPGroup (p := 3) (G := G)).card_eq_or_dvd with h | h
    · exact Or.inl h
    · exact Or.inr (le_antisymm hsmall (Nat.le_of_dvd Nat.card_pos h))
  let : IsCyclic N := by
    rcases hcases with h | h
    · exact isCyclic_of_orderOf_eq_card (1 : N) (by simp [h])
    · exact isCyclic_of_prime_card h
  have haut : ¬ 4 ∣ Nat.card (MulAut N) := by
    rw [IsCyclic.card_mulAut]
    rcases hcases with h | h <;> rw [h] <;> decide
  let f : G →* MulAut N := MulAut.conjNormal
  have hk : f.ker ≤ N := by
    apply le_trans ?_ hcentral
    intro g hg
    apply mem_centralizer_iff.mpr
    intro x hx
    have h := congrArg (fun a : MulAut N => (a ⟨x, hx⟩ : G)) hg
    change g * x * g⁻¹ = x at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hcop : Nat.Coprime 4 (Nat.card f.ker) := by
    apply Nat.Coprime.of_dvd_right (card_dvd_of_le hk)
    rcases hcases with h | h <;> rw [h] <;> decide
  apply haut
  apply dvd_trans _ f.range.card_subgroup_dvd_card
  apply hcop.dvd_of_dvd_mul_left
  rwa [← index_ker, card_mul_index]

/-- A normal solvable subgroup supplies a core normalized by its whole
overgroup, rather than only by a chosen solvable supplement. -/
theorem pCore_ne_bot_of_solvable_normal_of_characteristic
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] (hne : N ≠ ⊥) :
    pCore p N ≠ ⊥ := by
  have hodd : pPrimeCore p N = ⊥ := by
    apply ((pPrimeCore p N).map_eq_bot_iff_of_injective N.subtype_injective).mp
    apply le_bot_iff.mp
    exact (pPrimeCore_map_subtype_le_pPrimeCore_of_normal p N).trans_eq
      (pPrimeCore_eq_bot_of_centralizer_pCore_le p hcentral)
  intro hcore
  have hfit : fittingSubgroup N = ⊥ := (Fitting_eq_pcore N p hodd).trans hcore
  have hc := (fitting_eq_bot_iff_card_eq_one_of_solvable N).mp hfit
  exact hne ((card_le_one_iff_eq_bot N).mp hc.le)

end Theory.GroupTheory
