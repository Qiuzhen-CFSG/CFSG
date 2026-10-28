module
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Local invariants of the S₃ quotients in the M₁₂ construction

The normal three-subgroup of S₃ is its own centralizer and equals its
three-core, so it is the generalized Fitting subgroup. A Sylow two-subgroup
has prime order and hence is cyclic, giving two-rank at most one. The
statements accept actual multiplicative equivalences and therefore apply
to intrinsic quotients without identifying their carrier types.

Source: the local quotient calculation in Aschbacher–Smith, E.4.3(1),
printed p.241 (PDF p.252).
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

private theorem card_s3_sylow (P : Sylow 2 (Equiv.Perm (Fin 3))) : Nat.card P = 2 := by
  rw [P.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]
  have hf : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  norm_num [hf]

private theorem card_s3_threeSylow (P : Sylow 3 (Equiv.Perm (Fin 3))) : Nat.card P = 3 := by
  rw [P.card_eq_multiplicity, Nat.card_perm, Nat.card_fin]
  norm_num [Nat.factorial]
  have hf : Nat.factorization 6 3 = 1 := by
    change Nat.factorization (3 * 2) 3 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  norm_num [hf]

private theorem card_a3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

private theorem s3_threeCore : pCore 3 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  have hl : alternatingGroup (Fin 3) ≤ pCore 3 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by simpa using card_a3)⟩
  apply (eq_of_le_of_card_ge hl _).symm
  let P : Sylow 3 (Equiv.Perm (Fin 3)) := default
  have hle := card_le_of_le (pCore_isPGroup.le_sylow_of_normal P)
  simpa only [card_s3_threeSylow, card_a3] using hle

private theorem s3_threeCore_selfCentralizing :
    centralizer (pCore 3 (Equiv.Perm (Fin 3)) : Set (Equiv.Perm (Fin 3))) ≤
      pCore 3 (Equiv.Perm (Fin 3)) := by
  rw [s3_threeCore]
  intro x hx
  have htest : ∀ x : Equiv.Perm (Fin 3),
      (∀ y : Equiv.Perm (Fin 3), y ∈ alternatingGroup (Fin 3) → y * x = x * y) →
        x ∈ alternatingGroup (Fin 3) := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact htest x hx

/-- The generalized Fitting subgroup of an actual S₃ model has order three. -/
theorem generalizedFitting_card_of_equiv_s3 {G : Type*} [Group G] [Finite G]
    (e : G ≃* Equiv.Perm (Fin 3)) : Nat.card (generalizedFitting G) = 3 := by
  have hc : centralizer (pCore 3 G : Set G) ≤ pCore 3 G := by
    intro x hx
    have he : e x ∈ pCore 3 (Equiv.Perm (Fin 3)) := by
      apply s3_threeCore_selfCentralizing
      intro y hy
      rw [← pCore_map_iso 3 e] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      change e z * e x = e x * e z
      simpa only [map_mul] using congrArg e (hx z hz)
    rw [← pCore_map_iso 3 e] at he
    obtain ⟨z, hz, he⟩ := he
    exact e.injective he ▸ hz
  rw [generalizedFitting_eq_pCore_of_selfCentralizing 3 hc]
  have hm := pCore_map_iso 3 e
  have hh := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) => Nat.card H) hm
  rw [card_map_of_injective e.injective, s3_threeCore, card_a3] at hh
  exact hh

/-- A group identified with S₃ has two-rank at most one. -/
theorem primeRank_two_le_one_of_equiv_s3 {G : Type*} [Group G]
    (e : G ≃* Equiv.Perm (Fin 3)) : primeRank 2 G ≤ 1 := by
  let P : Sylow 2 (Equiv.Perm (Fin 3)) := default
  have hP : IsCyclic P := isCyclic_of_prime_card (card_s3_sylow P)
  exact P.primeRank_le_one_of_surjective hP e.symm.toMonoidHom e.symm.surjective

end Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
