module

public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# Removing two and the defining prime from a central kernel

An odd central kernel has no two-part. Trivial p-core excludes p from that
kernel, since a central element of order p generates a normal p-subgroup.
Thus a support bound on the remaining primes either makes the covering map
injective or makes its kernel an r-group. The maps remain the original maps
of finite perfect central covers.

Source: the central-cover deduction in Aschbacher–Smith A.2.17, printed p.39.
The actual model-specific support bounds are separate mathematical inputs.
-/

public section

open Subgroup
namespace PerfectCentralCovering

variable {E G : Type*} [Group E] [Group G]

/-- The original central quotient followed by an actual model equivalence. -/
@[expose] def centerQuotientCover [Group.IsPerfect E]
    (e : E ⧸ center E ≃* G) : Cover E G where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center E))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
  isPerfect := inferInstance
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Changing the quotient model does not change the literal covering kernel. -/
@[simp] theorem centerQuotientCover_ker [Group.IsPerfect E]
    (e : E ⧸ center E ≃* G) :
    (centerQuotientCover e).toMonoidHom.ker = center E := by
  change (e.toMonoidHom.comp (QuotientGroup.mk' (center E))).ker = _
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

variable [Finite E]

/-- Oddness and trivial p-core remove the two possible kernel primes. -/
theorem Cover.ker_eq_bot_of_odd_of_pCore_eq_bot
    (f : Cover E G) {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (hcore : pCore p E = ⊥)
    (hsupport : ∀ r : ℕ, r.Prime → r ∣ Nat.card f.toMonoidHom.ker →
      r = 2 ∨ r = p) : f.toMonoidHom.ker = ⊥ := by
  apply Subgroup.card_eq_one.mp
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro r hr hd
  rcases hsupport r hr hd with rfl | rfl
  · exact hodd.not_two_dvd_nat hd
  · exact not_dvd_card_central_of_pCore_eq_bot hcore
      f.toMonoidHom.ker f.ker_le_center hd

/-- If only one other prime is possible, the surviving kernel is an r-group. -/
theorem Cover.kernel_isPGroup_of_odd_of_pCore_eq_bot
    (f : Cover E G) {p r : ℕ} [Fact p.Prime] (hr : r.Prime)
    (hodd : Odd (Nat.card f.toMonoidHom.ker)) (hcore : pCore p E = ⊥)
    (hsupport : ∀ s : ℕ, s.Prime → s ∣ Nat.card f.toMonoidHom.ker →
      s = 2 ∨ s = p ∨ s = r) : IsPGroup r f.toMonoidHom.ker := by
  apply (isPGroup_iff_primeFactors_card_subset hr.ne_zero).mpr
  intro s hs
  obtain ⟨hsprime, hsdvd, _⟩ := Nat.mem_primeFactors.mp hs
  rcases hsupport s hsprime hsdvd with rfl | rfl | rfl
  · exact (hodd.not_two_dvd_nat hsdvd).elim
  · exact (not_dvd_card_central_of_pCore_eq_bot hcore
      f.toMonoidHom.ker f.ker_le_center hsdvd).elim
  · exact Nat.mem_primeFactors.mpr ⟨hr, dvd_rfl, hr.ne_zero⟩

end PerfectCentralCovering
