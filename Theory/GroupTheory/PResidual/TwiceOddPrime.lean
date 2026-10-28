module
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Two-residuals over a quotient of order twice an odd prime

A prime-order subgroup has index two in a group of order 2q. Its generator
belongs to the two-residual, and its two-group quotient gives the reverse
containment. The residual therefore has order q and trivial two-core.
Transport through a surjection with two-group kernel retains the intrinsic
core quotient of the residual.

Source application: the literal dihedral factors in Aschbacher--Smith
14.6.12 and 14.6.15, printed pp.1031 and 1034. The concrete consumer is
OddNormalizer.Quintic.ModuleGeometry.ResidualFactors.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]

/-- A group of order 2q has two-residual of order q when q is an odd prime. -/
theorem card_twoResidual_of_card_twice_odd_prime {q : ℕ} [Fact q.Prime]
    (ho : Odd q) (hc : Nat.card G = 2*q) : Nat.card (pResidual 2 G) = q := by
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := G) q (by rw [hc]; exact dvd_mul_left _ _)
  let K := zpowers g
  have hK : Nat.card K = q := by rw [Nat.card_zpowers,hg]
  have hi : K.index = 2 := by
    have hh := K.card_mul_index
    rw [hK,hc,mul_comm 2 q] at hh
    exact Nat.eq_of_mul_eq_mul_left (Fact.out : q.Prime).pos hh
  let : K.Normal := normal_of_index_eq_two hi
  have he : pResidual 2 G = K := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨inferInstance,IsPGroup.of_card (n := 1) ?_⟩
      change K.index = 2^1
      simpa using hi
    · apply zpowers_le.mpr
      apply mem_pResidual_of_orderOf_coprime
      rw [hg]
      exact ho.coprime_two_left
  rwa [he]

/-- The odd prime-order residual has trivial two-core. -/
theorem card_twoResidual_coreQuotient_of_card_twice_odd_prime {q : ℕ} [Fact q.Prime]
    (ho : Odd q) (hc : Nat.card G = 2*q) :
    Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = q := by
  have hr := card_twoResidual_of_card_twice_odd_prime ho hc
  have hcore : pCore 2 (pResidual 2 G) = ⊥ := by
    rcases (pCore_isPGroup (p := 2) (G := pResidual 2 G)).card_eq_or_dvd with h | h
    · exact card_eq_one.mp h
    · have hd := h.trans (pCore 2 (pResidual 2 G)).card_subgroup_dvd_card
      rw [hr] at hd
      exact (ho.not_two_dvd_nat hd).elim
  rw [hcore,Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  exact hr

/-- A two-group kernel preserves this intrinsic residual core quotient. -/
theorem card_twoResidual_coreQuotient_of_two_kernel {q : ℕ} [Fact q.Prime]
    (ho : Odd q) (f : G →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hc : Nat.card D = 2*q) :
    Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = q := by
  rw [Nat.card_congr (f.pResidualCoreQuotientEquiv hf hk).toEquiv]
  exact card_twoResidual_coreQuotient_of_card_twice_odd_prime ho hc

end Subgroup
