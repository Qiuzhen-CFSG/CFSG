module

public import Theory.GroupTheory.CharacteristicTwoOddAction
public import Theory.GroupTheory.Hall.OddSylowComplement
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Sylow index controlled by odd automorphisms of the two-core

Suppose the two-core of a finite solvable group is self-centralizing and
every odd subgroup of its automorphism group has order dividing three.
An odd Hall complement acts faithfully on the core, so every Sylow
two-subgroup has index one or three. The action on three cosets then
bounds its relative index over the core by two.

This separates the Hall and permutation-action argument from calculations
of automorphisms of particular two-groups. See Janko–Thompson, Math. Z. 113
(1970), §4, p.392, and the standard three-coset action.
-/

open Subgroup

/-- Odd automorphisms of a self-centralizing two-core bound the Sylow index. -/
public theorem Sylow.index_dvd_three_of_pCore_odd_automorphisms
    {K : Type*} [Group K] [Finite K] (hsolv : Group.IsSolvable K)
    (hchar : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (haut : ∀ U : Subgroup (MulAut (pCore 2 K)), Odd (Nat.card U) → Nat.card U ∣ 3)
    (T : Sylow 2 K) : (T : Subgroup K).index ∣ 3 := by
  obtain ⟨U, hodd, hcomp⟩ := exists_odd_complement_sylow_two hsolv T
  let action : U →* MulAut (pCore 2 K) := MulAut.conjNormal.comp U.subtype
  have hi : Function.Injective action :=
    odd_subgroup_conj_twoCore_injective hchar U hodd.coprime_two_left
  let e : U ≃* action.range := MonoidHom.ofInjective hi
  have hoddA : Odd (Nat.card action.range) := (Nat.card_congr e.toEquiv) ▸ hodd
  rw [hcomp.symm.index_eq_card, Nat.card_congr e.toEquiv]
  exact haut action.range hoddA

/-- A Sylow two-subgroup has relative index at most two over a
self-centralizing core with odd automorphism subgroups of order at most three. -/
public theorem Sylow.relIndex_pCore_le_two_of_odd_automorphisms
    {K : Type*} [Group K] [Finite K] (hsolv : Group.IsSolvable K)
    (hchar : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (haut : ∀ U : Subgroup (MulAut (pCore 2 K)), Odd (Nat.card U) → Nat.card U ∣ 3)
    (T : Sylow 2 K) : (pCore 2 K).relIndex T ≤ 2 := by
  have hle : pCore 2 K ≤ T := pCore_isPGroup.le_sylow_of_normal _
  by_cases heq : pCore 2 K = (T : Subgroup K)
  · simp [heq]
  have hproper := lt_of_le_of_ne hle heq
  have hindex : (T : Subgroup K).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp
      (T.index_dvd_three_of_pCore_odd_automorphisms hsolv hchar haut) with h | h
    · have ht : (T : Subgroup K) = ⊤ := index_eq_one.mp h
      have hnormal : (T : Subgroup K).Normal := ht ▸ inferInstance
      exact (heq (le_antisymm hle (le_sSup ⟨hnormal, T.isPGroup'⟩))).elim
    · exact h
  obtain ⟨e⟩ := sylow_index_three_core_quotient T hindex hproper
  have hquot : (pCore 2 K).index = 6 := by
    change Nat.card (K ⧸ pCore 2 K) = 6
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hmul := relIndex_mul_index hle
  rw [hindex, hquot] at hmul
  omega
