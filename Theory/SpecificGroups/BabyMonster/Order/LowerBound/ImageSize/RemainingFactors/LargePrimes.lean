module

public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.BlockChecks
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Trace
public import Theory.SpecificGroups.BabyMonster.Order.LowerBound.ImageSize.RemainingFactors.LargePrimes.Words

/-!
# Assembly of the seven larger prime divisors

Each concrete packed orbit certificate gives a prime divisor of the order of
the fixed standard matrix subgroup. This module assembles those implications.
The seven concrete certificates are still required; this conditional theorem
makes their exact remaining mathematical obligations explicit.

The words come from the ATLAS Baby Monster class representatives, recorded in
`RemainingFactors/source/README.md`. Their proposed source orders are not used.
-/

public section

namespace BabyMonster.OrderLowerBound.RemainingFactors

/-- Assemble checked packed-vector orbits for the seven larger primes. -/
theorem largePrimes_dvd_of_certificates
    (ha : atlasA ^ 2 = 1) (hb : atlasB ^ 3 = 1)
    (h11 : LargePrimes.Certificate 11 LargePrimes.word11)
    (h13 : LargePrimes.Certificate 13 LargePrimes.word13)
    (h17 : LargePrimes.Certificate 17 LargePrimes.word17)
    (h19 : LargePrimes.Certificate 19 LargePrimes.word19)
    (h23 : LargePrimes.Certificate 23 LargePrimes.word23)
    (h31 : LargePrimes.Certificate 31 LargePrimes.word31)
    (h47 : LargePrimes.Certificate 47 LargePrimes.word47) :
    11 ∣ Nat.card (standardImage ha hb) ∧
    13 ∣ Nat.card (standardImage ha hb) ∧
    17 ∣ Nat.card (standardImage ha hb) ∧
    19 ∣ Nat.card (standardImage ha hb) ∧
    23 ∣ Nat.card (standardImage ha hb) ∧
    31 ∣ Nat.card (standardImage ha hb) ∧
    47 ∣ Nat.card (standardImage ha hb) := by
  exact ⟨LargePrimes.prime_dvd_of_certificate ha hb (by decide) h11,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h13,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h17,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h19,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h23,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h31,
    LargePrimes.prime_dvd_of_certificate ha hb (by decide) h47⟩

end BabyMonster.OrderLowerBound.RemainingFactors
