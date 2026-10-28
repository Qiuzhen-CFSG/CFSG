module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrder
public import Theory.GroupTheory.CharacteristicTwoOddAction
public import Theory.GroupTheory.Hall.OddSylowComplement
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Sylow index above a small self-centralizing two-core

Let a finite solvable group have a self-centralizing, nonabelian two-core
of order less than thirty-two. Every odd subgroup embeds in the automorphism
group of that core, so its order divides three. Hall's theorem gives an odd
complement to any Sylow two-subgroup. If that Sylow is not normal, its index
is three. The three-coset action then identifies the core quotient with the
symmetric group on three letters; the Sylow has relative order two over the
core.

Sources: the small-core automorphism bound in Stellmacher (8.6), printed
p.42, and the standard three-coset action, as in Parrott (1972), p.677.
-/

open Subgroup

/-- A nonnormal Sylow two-subgroup has relative index two over a
self-centralizing nonabelian core of order less than thirty-two. -/
public theorem Sylow.relIndex_pCore_eq_two_of_small_nonabelian
    {K : Type*} [Group K] [Finite K] (hsolv : Group.IsSolvable K)
    (hchar : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hnoncomm : ¬ IsMulCommutative (pCore 2 K))
    (hbound : Nat.card (pCore 2 K) < 32)
    (T : Sylow 2 K) (hnormal : ¬ (T : Subgroup K).Normal) :
    (pCore 2 K).relIndex T = 2 := by
  have hactors (U : Subgroup K) (hodd : Odd (Nat.card U)) : Nat.card U ∣ 3 := by
    let action : U →* MulAut (pCore 2 K) := MulAut.conjNormal.comp U.subtype
    have hi : Function.Injective action :=
      odd_subgroup_conj_twoCore_injective hchar U hodd.coprime_two_left
    let e : U ≃* action.range := MonoidHom.ofInjective hi
    have hoddA : Odd (Nat.card action.range) := (Nat.card_congr e.toEquiv) ▸ hodd
    have hd := SmallNonabelianTwoGroup.small_nonabelian_two_group_odd_order_bound
      pCore_isPGroup hnoncomm (Nat.le_of_lt hbound)
      (fun hc => (Nat.ne_of_lt hbound hc).elim) action.range hoddA
    simpa only [if_neg (Nat.ne_of_lt hbound), ← Nat.card_congr e.toEquiv] using hd
  obtain ⟨U, hodd, hcomp⟩ := exists_odd_complement_sylow_two hsolv T
  have hindexdvd : (T : Subgroup K).index ∣ 3 := by
    rw [hcomp.symm.index_eq_card]
    exact hactors U hodd
  have hindex : (T : Subgroup K).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hindexdvd with h | h
    · exact (hnormal (index_eq_one.mp h ▸ (inferInstance : (⊤ : Subgroup K).Normal))).elim
    · exact h
  have hle : pCore 2 K ≤ T := pCore_isPGroup.le_sylow_of_normal _
  have hproper : pCore 2 K < (T : Subgroup K) := lt_of_le_of_ne hle (by
    intro h
    exact hnormal (h ▸ (inferInstance : (pCore 2 K).Normal)))
  obtain ⟨e⟩ := sylow_index_three_core_quotient T hindex hproper
  have hquot : (pCore 2 K).index = 6 := by
    change Nat.card (K ⧸ pCore 2 K) = 6
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  have hmul := relIndex_mul_index hle
  rw [hindex, hquot] at hmul
  omega
