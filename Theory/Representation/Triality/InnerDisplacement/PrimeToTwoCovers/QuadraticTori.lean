module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.Reduction
public import Theory.SpecificGroups.Triality.QuadraticTori.ConcreteWitness

/-!
# Quadratic-torus primes in binary triality central covers

For `q = 2 ^ n`, the concrete split and nonsplit rank-one products in
`Standard.QuadraticTori` give the local odd-Sylow geometry at every prime
`p > 3` dividing `q ^ 2 - 1`.  The perfect-central-cover transfer then
excludes `p` from the kernel of every finite perfect central cover of the
binary triality carrier.  The final theorem applies this calculation to the
literal projection of a finite quasisimple group through its center.

The geometric input is the actual torus and normalizer construction in
`Theory/SpecificGroups/Triality/QuadraticTori/ConcreteWitness.lean`; no
multiplier bound or covering certificate is used here.

Source: GLS3, §6.1, Theorem 6.1.4 and Tables 6.1.2--3, with the torus
conventions of §2.6 in `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

namespace Triality.InnerDisplacement.PrimeToTwoCovers.QuadraticTori

open PerfectCentralCovering
open PerfectCentralCovering.OddSylow

/-- Every quadratic-torus prime is excluded from an arbitrary finite perfect
central cover of the binary triality carrier. -/
theorem not_dvd_card_kernel {E : Type*} [Group E] [Finite E]
    (n : ℕ) (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 - 1)
    (f : Cover E (Standard.BinaryCarrier n hn)) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  exact (Standard.QuadraticTori.geometry n hn hp hd).not_dvd_card_kernel (by omega) f

/-- The same quadratic-prime exclusion for the literal map
`R → R / center R` of a finite quasisimple triality cover. -/
theorem not_dvd_card_center {R : Type*} [Group R] [Finite R]
    [Theory.GroupTheory.IsQuasisimple R] (n : ℕ) (hn : 0 < n)
    (hmodel : Standard.IsTrialityGroupAt (2 ^ n) (R ⧸ Subgroup.center R))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hd : p ∣ (2 ^ n) ^ 2 - 1) :
    ¬ p ∣ Nat.card (Subgroup.center R) := by
  obtain ⟨e⟩ := (Standard.isTrialityGroupAt_binary_iff _ n hn).mp hmodel
  rw [← centralQuotientCover_ker e]
  exact not_dvd_card_kernel n hn hp hd (centralQuotientCover e)

end Triality.InnerDisplacement.PrimeToTwoCovers.QuadraticTori
