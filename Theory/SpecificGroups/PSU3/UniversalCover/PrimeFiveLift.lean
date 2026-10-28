module

public import Theory.SpecificGroups.PSU3.UniversalCover.OddPartDescent
public import Theory.SpecificGroups.PSU3.UniversalCover.OddKernelBound.OddCrossCharacteristic

/-!
# The prescribed SU₃(5) lift to a quasisimple group with trivial two-core

For a Hermitian form over a field of order 25, the odd-primary kernel
bounds leave only the scalar factor of order three. The defining prime
is excluded by the prime-field theorem; every other odd prime except
three is excluded because it does not divide six, and nine is excluded
because it does not divide six. Odd-part descent then kills the remaining
comparison two-kernel in any target with trivial two-core.

The resulting surjection from the actual special-unitary group retains
the specified projection to the projective group. Neither universality of
the special-unitary projection nor triviality of its scalar kernel is needed.

Source: Aschbacher–Smith I.1.3(2), I.1.4(2), printed pp.407–408;
the source application is Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11, used in Aschbacher–Smith K.2, printed p.453.
-/

public section

open Subgroup Theory.GroupTheory PerfectCentralCovering BenderSuzuki.MatrixGroups

namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.PrimeFiveLift

universe u v
variable {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)

/-- The scalar cover of PSU₃(5) maps onto every given quasisimple cover
with trivial two-core, over its original projective projection. -/
theorem exists_lift
    (hcard : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {L : Type v} [Group L] [Finite L] [IsQuasisimple L]
    (f : L →* ProjectiveSpecialUnitaryMatrixGroup J) (hf : Function.Surjective f)
    (hcore : pCore 2 L = ⊥) :
    ∃ k : J.specialSubgroup →* L, Function.Surjective k ∧
      f.comp k = J.specialToProjective := by
  let := projective_isQuasisimple J (by decide : 2 < 5) hcard hconj
  apply OddPartDescent.exists_lift_odd J (p := 5) (e := 1)
    (by decide) (by decide) (by decide) (by decide)
    (by simpa only [pow_one] using hcard)
    (by simpa only [pow_one] using hconj) _ _ _ f hf hcore
  · intro he
    omega
  · intro r hr hr2 hr3 hr5
    apply OddKernelBound.OddCrossCharacteristic.not_dvd_kernel_of_not_dvd_add_one
      J (p := 5) (e := 1) (by decide) (by decide) hr hr2 hr3 hr5
      (by simpa only [pow_one] using hcard)
      (by simpa only [pow_one] using hconj) _ (universalCover _)
    change ¬ r ∣ 2 * 3
    intro hd
    rcases hr.dvd_mul.mp hd with h2 | h3
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2)
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
  · intro _
    exact OddKernelBound.OddCrossCharacteristic.not_nine_dvd_kernel_of_not_nine_dvd_add_one
      J (by decide : 1 < 5) hcard hconj (by decide) (by decide) (universalCover _)

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.PrimeFiveLift
