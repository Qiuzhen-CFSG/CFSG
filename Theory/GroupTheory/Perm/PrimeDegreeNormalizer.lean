module

public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Normalizers of prime-order Sylow subgroups in prime degree

A permutation of prime order equal to the degree is a full cycle. Its centralizer
consists of its powers, so a prime-order Sylow subgroup in a faithful action of
that degree is self-centralizing. Conjugation then embeds its automizer into the
automorphisms of the cyclic subgroup, bounding the normalizer order by divisibility.

This is the elementary permutation-group input to the odd-order obstruction in
Aschbacher--Smith, *The Classification of Quasithin Groups*, Lemma 5.2.21.
-/

namespace Theory.GroupTheory

open Subgroup Equiv.Perm

/-- A prime-order element acting faithfully on that many points is self-centralizing. -/
public theorem centralizer_eq_zpowers_of_prime_degree
    {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (f : G →* Equiv.Perm (Fin p)) (hf : Function.Injective f)
    (x : G) (hx : orderOf x = p) :
    centralizer ({x} : Set G) = zpowers x := by
  classical
  have ho : orderOf (f x) = p := (orderOf_injective f hf x).trans hx
  have hc : (f x).IsCycle := isCycle_of_prime_order'' (by simpa using hp) (by simpa using ho)
  have hs : (f x).support = Finset.univ :=
    (Finset.card_eq_iff_eq_univ _).mp (by simpa using hc.orderOf.symm.trans ho)
  apply le_antisymm
  · intro y hy
    have hcomm : Commute (f y) (f x) := by
      apply Commute.map
      exact mem_centralizer_singleton_iff.mp hy
    obtain ⟨hpres, hpow⟩ := hc.commute_iff.mp hcomm
    have he : ofSubtype ((f y).subtypePerm hpres) = f y := by
      apply Equiv.ext
      intro a
      exact ofSubtype_subtypePerm_of_mem hpres (by rw [hs]; exact Finset.mem_univ a)
    rw [he] at hpow
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hpow
    exact mem_zpowers_iff.mpr ⟨n, hf (by simpa using hn)⟩
  · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

/-- A Sylow subgroup of prime order in a faithful action of that degree is self-centralizing. -/
public theorem prime_degree_sylow_self_centralizing
    {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (f : G →* Equiv.Perm (Fin p)) (hf : Function.Injective f)
    (P : Sylow p G) (hP : Nat.card P = p) :
    centralizer (P : Set G) = (P : Subgroup G) := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := P)
  have hxo : orderOf (x : G) = p := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hx, hP]
  have hz : zpowers (x : G) = (P : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact zpowers_le.mpr x.property
    · rw [Nat.card_zpowers, hxo, hP]
  change centralizer ((P : Subgroup G) : Set G) = _
  rw [← hz, zpowers_eq_closure, centralizer_closure]
  exact (centralizer_eq_zpowers_of_prime_degree hp.out f hf x hxo).trans
    (zpowers_eq_closure _)

/-- The normalizer order is the prime degree times a divisor of one less than that degree. -/
public theorem prime_degree_normalizer_card
    {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (f : G →* Equiv.Perm (Fin p)) (hf : Function.Injective f)
    (P : Sylow p G) (hP : Nat.card P = p) :
    ∃ m, m ∣ p - 1 ∧ Nat.card (normalizer (P : Set G)) = p * m := by
  exact ⟨_, P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP,
    P.normalizer_card_of_self_centralizing hP
      (prime_degree_sylow_self_centralizing f hf P hP)⟩

end Theory.GroupTheory
