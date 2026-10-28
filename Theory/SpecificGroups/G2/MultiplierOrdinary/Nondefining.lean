module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.SplitTorus
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary

/-!
# All nondefining primes in the even-characteristic G₂ universal kernel

For every finite field F of characteristic two and order q > 4, no odd prime
divides the kernel of the canonical universal perfect central cover of G₂(F).
The prime three uses the full torus normalizer calculation, with arbitrary
three-adic valuation of q − 1 or q + 1. For primes greater than three, the
factorization q² − 1 = (q − 1)(q + 1) selects the split or nonsplit product
torus; the remaining primes in the group order have cyclic Sylow subgroups.
Primes absent from the group order are also excluded by central transfer.
Every torus, action and covering here belongs to the actual octonion model.

The resulting two-group property is the ordinary-field multiplier input to
Chapter 13's marked action-kernel reduction. Triviality of the entire kernel
also requires the independent defining-prime calculation; the application in
`Nondefining.Assembly` leaves only that calculation's positive-root relations.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419),
and GLS III §6.1. The concrete octonion model and its group-order and torus
results are attributed ATLAS ports; see LICENSES/ATLAS.txt.
-/

public section

namespace Atlas.G2.MultiplierOrdinary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

namespace Nondefining

variable [CharP F 2]

/-- The complete nondefining-prime calculation, including the noncyclic
Sylow-three branch, for the literal canonical universal kernel. -/
theorem not_dvd_card_universal_kernel (hF : 4 < Nat.card F)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  by_cases hr3 : r = 3
  · subst r
    exact ThreePrimary.universal_not_three_dvd_kernel hF
  have hrlarge : 3 < r := by have := hr.two_le; omega
  let : Fact r.Prime := ⟨hr⟩
  by_cases hquad : r ∣ Nat.card F ^ 2 - 1
  · have hfactor : Nat.card F ^ 2 - 1 =
        (Nat.card F - 1) * (Nat.card F + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
    rw [hfactor] at hquad
    rcases hr.dvd_mul.mp hquad with hsplit | hnonsplit
    · exact not_dvd_card_universal_kernel_of_dvd_sub_one hF hr2 hr3 hsplit
    · exact not_dvd_card_universal_kernel_of_dvd_add_one hF hrlarge hnonsplit
  by_cases horder : r ∣ Nat.card (Model F)
  · exact CyclotomicSylow.not_dvd_card_universal_kernel hF hrlarge hquad horder
  · exact not_dvd_card_universal_kernel_of_not_dvd_model hF hr2 horder

/-- The precise ordinary-field multiplier property consumed by the marked
G₂ action-kernel reduction: the canonical universal kernel is a two-group. -/
theorem universalKernel_isPGroup (hF : 4 < Nat.card F) :
    IsPGroup 2 (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro r hr
  obtain ⟨hrprime, hrdiv, _⟩ := Nat.mem_primeFactors.mp hr
  have heq : r = 2 := by
    by_contra hr2
    exact not_dvd_card_universal_kernel hF hrprime hr2 hrdiv
  norm_num [heq]

end Nondefining

/-- The same exclusion in the cardinality form of the ordinary source
family G₂(2ⁿ), n ≥ 3; characteristic two is derived from the field order. -/
theorem even_universal_not_dvd_kernel {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 4 < Nat.card F := by
    have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  exact Nondefining.not_dvd_card_universal_kernel hlarge hr hr2

end Atlas.G2.MultiplierOrdinary

end
