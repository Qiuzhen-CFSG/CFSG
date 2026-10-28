module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddNondefining

/-!
# Nondefining primes in both ordinary G₂ universal kernels

This interface assembles the two ordinary source families for the literal
canonical universal projection onto the split-octonion group. In characteristic
two the field order is greater than four; in odd characteristic the field has
prime order greater than three. Every nondefining prime is excluded, including
three in both families and two in the odd family.

The imported proofs use central-cover transfer from the actual split,
quadratic and cubic tori. The noncyclic Sylow-three case uses torus normalizers,
and the odd-field Sylow-two case uses the orthogonal subgroup and involution
fusion. Their concrete local witnesses are constructed in those modules.
Consequently the odd-prime universal kernel is a p-group, just as the even
kernel is a two-group. The defining-prime exclusion remains independent;
`NondefiningPrimes.Assembly` connects these results to the positive-root
relations used by the ordinary-kernel assembly.

Source: Aschbacher–Smith A.2.2–A.2.4, printed p.33 (PDF p.44), and
I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419); GLS III §6.1.
The concrete model constructions are attributed ATLAS ports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.NondefiningPrimes

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- Every nondefining prime is excluded from the canonical kernel in the
ordinary characteristic-two range, including the prime three. -/
theorem even_not_dvd_card_universal_kernel [CharP F 2]
    (hF : 4 < Nat.card F) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker :=
  Nondefining.not_dvd_card_universal_kernel hF hr hr2

/-- Every nondefining prime is excluded from the canonical kernel in the
ordinary odd-prime range, including the primes two and three. -/
theorem prime_not_dvd_card_universal_kernel
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker :=
  prime_universal_not_dvd_kernel hF hp hr hrp

/-- Only the defining prime can divide the ordinary odd-prime multiplier.
This uses finiteness of the actual universal cover, with no multiplier bound. -/
theorem prime_universalKernel_isPGroup
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p) :
    IsPGroup p (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  apply (isPGroup_iff_primeFactors_card_subset (by omega : p ≠ 0)).mpr
  intro r hr
  obtain ⟨hrprime, hrdiv, _⟩ := Nat.mem_primeFactors.mp hr
  have heq : r = p := by
    by_contra hrp
    exact prime_not_dvd_card_universal_kernel hF hp hrprime hrp hrdiv
  subst r
  exact Nat.mem_primeFactors.mpr ⟨hrprime, dvd_rfl, by omega⟩

end Atlas.G2.MultiplierOrdinary.NondefiningPrimes

end
