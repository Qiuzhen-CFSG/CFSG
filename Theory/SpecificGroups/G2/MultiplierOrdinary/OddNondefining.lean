module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddNondefiningReduction
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary

/-!
# Nondefining primes in the ordinary odd-prime G₂ multiplier

For a field of prime order p > 3, every prime r different from p is absent
from the kernel of the canonical universal projection onto the actual
split-octonion automorphism group.

The two-primary orthogonal-subgroup calculation and the three-primary torus
normalizer calculation handle r = 2 and r = 3. For r > 3 the split and
quadratic tori handle divisors of p − 1 and p + 1. Every remaining prime
in the group order has cyclic Sylow subgroups in a cubic or twisted cubic
torus. Primes absent from the group order are excluded by the same cyclic
Sylow transfer. All local geometric inputs are discharged by the imported
constructions; only the defining-prime calculation remains for the full
ordinary multiplier entry.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419),
with the odd-prime range from A.2.2–A.2.4; GLS III §6.1.
-/

public section

namespace Atlas.G2.MultiplierOrdinary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- Every nondefining prime, including two and three, is excluded from the
literal universal-cover kernel in the ordinary odd-prime source range. -/
theorem prime_universal_not_dvd_kernel
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  apply OddNondefining.prime_universal_not_dvd_kernel_of_local_calculations hF hp
    (OddTwoPrimary.universal_not_two_dvd_kernel hF hp)
    (OddThreePrimary.prime_universal_not_three_dvd_kernel hF hp) ?_ hr hrp
  intro s hs hslarge hsp hminus horder
  let : Fact s.Prime := ⟨hs⟩
  by_cases hplus : s ∣ p + 1
  · exact OddQuadraticTorus.prime_universal_not_dvd_kernel_of_quadratic
      hF hp hslarge hplus
  have hquad : ¬ s ∣ p ^ 2 - 1 := by
    have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p (by omega)
      have hsubsq := Nat.sub_add_cancel hsq
      nlinarith
    rw [hfactor]
    exact hs.not_dvd_mul hminus hplus
  exact OddCyclotomicSylow.universal_not_dvd_kernel hF hp hslarge hsp hquad horder

end Atlas.G2.MultiplierOrdinary

end
