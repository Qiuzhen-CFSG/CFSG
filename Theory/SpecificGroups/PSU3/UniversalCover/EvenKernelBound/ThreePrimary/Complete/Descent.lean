module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.Complete
public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent

/-!
# The binary unitary descent application of the three-primary bound

The proved universal-kernel bound discharges the nine-exclusion premise of
`OddPartDescent.exists_lift_even`. Thus the actual SU₃ projection lifts onto
every quasisimple cover with trivial two-core once primes above three have
been excluded from the universal kernel. That independent prime exclusion
remains explicit; the three-primary calculation supplies no assumption
about two or larger primes.

This extension is separate from the narrow kernel-bound module so that
the full even-kernel assembly can import that bound without an import cycle.
The map identity uses the original Hermitian form and projective quotient.

Source: Aschbacher–Smith A.2.17, A.3.6 and I.1.3(2);
GLS III, Theorem 6.1.4 and Tables 6.1.2–3.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddPartDescent

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The literal scalar projection lifts with its factorization preserved.
Only the independent exclusion of primes above three remains to be supplied. -/
theorem exists_lift_even_of_large_prime_exclusion {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hlarge : ∀ r : ℕ, r.Prime → 3 < r →
      ¬ r ∣ Nat.card (universalProjection (ProjectiveSpecialUnitaryMatrixGroup J)).ker)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  exact exists_lift_even J hn hcard hconj hlarge
    (fun hodd => EvenKernelBound.ThreePrimary.not_nine_dvd_universal_kernel
      J hn hodd hcard hconj) f hf hcore

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.OddPartDescent
