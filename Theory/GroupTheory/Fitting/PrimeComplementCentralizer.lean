module

public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Self-centralization of the prime-complement core

If a finite group has trivial p-core, its Fitting subgroup lies in its
p-complement core: every other prime core has order coprime to p. In a
solvable group, Fitting self-centralization therefore makes the p-complement
core self-centralizing. Consequently no nontrivial p-subgroup centralizes it.

This supplies hypothesis S1 of Kurzweil–Stellmacher, *The Theory of Finite
Groups*, §9.3, for the solvable binary offender argument. The prime-core
calculation also occurs privately in `MixedCoreOvergroup.lean`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]

/-- With trivial p-core, all the prime cores contributing to the Fitting
subgroup have order coprime to p. -/
theorem fitting_le_pPrimeCore_of_pCore_eq_bot
    (hcore : pCore p G = ⊥) : fittingSubgroup G ≤ pPrimeCore p G := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun prime => ?_
  by_cases heq : prime.val.val = p
  · rw [heq, hcore]
    exact bot_le
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    obtain ⟨exponent, hcard⟩ :=
      (pCore_isPGroup (p := prime.val.val) (G := G)).exists_card_eq
    rw [hcard]
    exact ((Nat.coprime_primes (Fact.out : p.Prime)
      (Nat.prime_of_mem_primeFactors prime.val.property)).mpr (Ne.symm heq)).pow_right _

/-- The p-complement core is self-centralizing in a finite solvable group
with trivial p-core. -/
theorem centralizer_pPrimeCore_le_of_pCore_eq_bot
    (hsolv : Group.IsSolvable G) (hcore : pCore p G = ⊥) :
    centralizer (pPrimeCore p G : Set G) ≤ pPrimeCore p G := by
  have hfit := fitting_le_pPrimeCore_of_pCore_eq_bot p hcore
  exact (centralizer_le hfit).trans
    ((centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv).trans hfit)

/-- A nontrivial p-subgroup acts nontrivially on the p-complement core. -/
theorem not_le_centralizer_pPrimeCore_of_isPGroup
    (hsolv : Group.IsSolvable G) (hcore : pCore p G = ⊥)
    {A : Subgroup G} (hA : IsPGroup p A) (hne : A ≠ ⊥) :
    ¬ A ≤ centralizer (pPrimeCore p G : Set G) := by
  intro hcentral
  have hle := hcentral.trans (centralizer_pPrimeCore_le_of_pCore_eq_bot p hsolv hcore)
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pPrimeCore p G)) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := p) (G := G)).pow_left n
  have hdis := disjoint_of_coprime_natCard hcop
  exact hne (le_bot_iff.mp ((le_inf le_rfl hle).trans hdis.le_bot))

end Subgroup
