module
public import Theory.GroupTheory.PerfectCentralCoverRank

/-!
# Odd kernels over groups of odd-prime rank at most one

An odd central kernel of a finite perfect cover is trivial when every odd
prime rank of the target is at most one. For each possible kernel prime,
the target has cyclic Sylow subgroups and transfer excludes that prime.

Source application: Aschbacher–Smith E.2.2(1), printed pp.215–216.
-/

public section
namespace PerfectCentralCovering
variable {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]

/-- Odd kernels vanish over a target with all odd-prime ranks at most one. -/
theorem Cover.ker_eq_bot_of_odd_of_odd_primeRank_le_one (f : Cover E G)
    (ho : Odd (Nat.card f.toMonoidHom.ker))
    (hr : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1) :
    f.toMonoidHom.ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hd
  have hp2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ hd)
  have hpo := hp.odd_of_ne_two hp2
  let : Fact p.Prime := ⟨hp⟩
  exact f.not_dvd_card_multiplier_of_odd_of_primeRank_le_one hpo (hr p hp hpo) hd
end PerfectCentralCovering
