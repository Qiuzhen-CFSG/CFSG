module

public import Theory.GroupTheory.PerfectCentralCover
public import Theory.GroupTheory.PCoreSurjective

/-!
# Eliminating odd kernels in perfect central covers

Transfer excludes a prime from the kernel of a perfect central cover when
the target's Sylow subgroups at that prime are cyclic. Excluding every odd
prime makes the kernel a two-group. If the target has trivial two-core, the
kernel is exactly the original two-core, giving an actual quotient equivalence.
An odd kernel is therefore trivial.

This is the covering argument in GLS, volume 2, Theorem 25.14, Steps 2--3,
based on Lemma 15.12(iv). The cyclic Sylow hypotheses are explicit: their
verification for the concrete PSL2 factors is a separate model argument.
These statements apply to one perfect factor; cyclicity is not asserted for
the odd Sylow subgroups of a product of two factors.
-/

@[expose] public section

open Subgroup
namespace PerfectCentralCovering

variable {H K : Type*} [Group H] [Group K] [Finite H] [Finite K]

/-- Cyclic odd Sylow subgroups of the target force a two-group kernel. -/
theorem Cover.kernel_isTwoGroup (f : Cover H K)
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p K, IsCyclic P) :
    IsPGroup 2 f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hdiv := Nat.dvd_of_mem_primeFactors hp
  let : Fact p.Prime := ⟨hprime⟩
  have heq : p = 2 := by
    by_contra hne
    exact f.not_dvd_card_multiplier_of_isCyclic_sylow (hcyclic p hne) hdiv
  simp [heq, Nat.prime_two]

/-- If the target has trivial two-core, the kernel is exactly the source two-core. -/
theorem Cover.kernel_eq_twoCore (f : Cover H K)
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p K, IsCyclic P)
    (hcore : pCore 2 K = ⊥) : f.toMonoidHom.ker = pCore 2 H := by
  have he := f.toMonoidHom.comap_pCore_of_ker_isPGroup f.surjective
    (f.kernel_isTwoGroup hcyclic)
  rw [hcore] at he
  exact he

/-- The resulting equivalence uses the intrinsic two-core of the source. -/
noncomputable def Cover.quotientTwoCoreEquiv (f : Cover H K)
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p K, IsCyclic P)
    (hcore : pCore 2 K = ⊥) : H ⧸ pCore 2 H ≃* K :=
  (QuotientGroup.quotientMulEquivOfEq (f.kernel_eq_twoCore hcyclic hcore).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)

/-- A perfect central cover of odd degree is trivial under the Sylow hypothesis. -/
theorem Cover.kernel_eq_bot_of_odd (f : Cover H K)
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p K, IsCyclic P)
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) : f.toMonoidHom.ker = ⊥ := by
  rcases (f.kernel_isTwoGroup hcyclic).card_eq_or_dvd with hcard | hdiv
  · exact Subgroup.card_eq_one.mp hcard
  · exact (hodd.not_two_dvd_nat hdiv).elim

end PerfectCentralCovering

end
