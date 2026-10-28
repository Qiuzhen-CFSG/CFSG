module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# Cubic subgroups normalized by symmetric-group Sylow subgroups

In degrees five through eight, a full Sylow two-subgroup can normalize a
nontrivial cubic subgroup only in degree seven, where its generator is a
single three-cycle. The proof computes the centralizer from the cycle
type and bounds the normalizer by twice that order. The two-part of the
factorial excludes every other case. No finite permutation enumeration
or group classification is used.

Source application: the symmetric-model sieve in Aschbacher–Smith,
C.5.12, printed p.163, following the transvection theorem G.6.4.
-/

public section

open Subgroup
namespace Equiv.Perm
private theorem cubic_normalizer_card_dvd {G : Type*} [Group G] [Finite G]
    (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1) :
    Nat.card (normalizer (zpowers c : Set G)) ∣
      Nat.card (centralizer ({c} : Set G)) * 2 := by
  let A := zpowers c
  have hker : Nat.card A.normalizerMonoidHom.ker = Nat.card (centralizer (A : Set G)) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (A : Set G))).toEquiv]
  have hprod := A.normalizerMonoidHom.ker.card_mul_index
  rw [index_ker, hker] at hprod
  have hdiv : Nat.card (normalizer (A : Set G)) ∣
      Nat.card (centralizer (A : Set G)) * Nat.card (MulAut A) := by
    rw [← hprod]
    exact Nat.mul_dvd_mul_left _ A.normalizerMonoidHom.range.card_subgroup_dvd_card
  have hcard : Nat.card A = 3 := by rw [Nat.card_zpowers]; exact orderOf_eq_prime hc hcne
  have hcen : centralizer (A : Set G) = centralizer ({c} : Set G) := by
    ext g
    simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h; exact h c (mem_zpowers c)
    · intro h x hx
      obtain ⟨k, rfl⟩ := hx
      exact (Commute.zpow_left (show Commute c g from h) k).eq
  simpa only [hcen, IsCyclic.card_mulAut, hcard, show Nat.totient 3 = 2 by decide] using hdiv

theorem degree_seven_of_sylow_normalizes_cubic {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8)
    (S : Sylow 2 (Perm (Fin n))) (c : Perm (Fin n)) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hS : (S : Subgroup (Perm (Fin n))) ≤ normalizer (zpowers c : Set (Perm (Fin n)))) :
    n = 7 ∧ c.cycleType = {3} := by
  classical
  have ho : orderOf c = 3 := orderOf_eq_prime hc hcne
  obtain ⟨k, hk⟩ := cycleType_prime_order (σ := c) (ho ▸ Nat.prime_three)
  rw [ho] at hk
  have hb := c.support.card_le_univ
  rw [← sum_cycleType, hk] at hb
  simp only [Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, Fintype.card_fin] at hb
  have hk1 : k ≤ 1 := by omega
  have hdiv := (Subgroup.card_dvd_of_le hS).trans (cubic_normalizer_card_dvd c hc hcne)
  rw [nat_card_centralizer, hk] at hdiv
  have hpow (m : ℕ) (hm : 2 ^ m ∣ n.factorial) : 2 ^ m ∣ Nat.card S := by
    apply S.pow_dvd_card_of_pow_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using hm
  interval_cases n <;> interval_cases k
  all_goals norm_num [Nat.factorial, Multiset.replicate_succ] at hdiv
  all_goals rw [← Nat.card_eq_fintype_card] at hdiv
  all_goals solve
    | exact ⟨rfl, by simpa using hk⟩
    | have hbad := (hpow 3 (by norm_num [Nat.factorial])).trans hdiv
      norm_num at hbad
    | have hbad := (hpow 4 (by norm_num [Nat.factorial])).trans hdiv
      norm_num at hbad
    | have hbad := (hpow 7 (by norm_num [Nat.factorial])).trans hdiv
      norm_num at hbad
end Equiv.Perm
