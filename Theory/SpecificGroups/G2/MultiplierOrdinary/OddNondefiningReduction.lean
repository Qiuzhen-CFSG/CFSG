module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddSplitTorus

/-!
# Remaining local calculations for ordinary odd-prime G₂ multipliers

The concrete split-torus calculation discharges every r > 3 dividing p − 1.
Cyclic Sylow transfer also removes every prime absent from the model order.
The exact source nondefining-prime conclusion therefore reduces to r = 2,
r = 3, and the primes in the actual group order outside p − 1.

This is conditional assembly, not a proof of the whole multiplier entry.
The small-prime and nonsplit calculations must still be supplied. No ordinary
matrix projection, centerlessness assertion or multiplier-table omission is
used in place of the literal universal-cover kernel.

Source: Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408 (PDF pp.418–419),
with the ordinary G₂(p), p prime and p > 3, range from A.2.2–A.2.4;
GLS III §6.1 gives the referenced multiplier calculation.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddNondefining

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- Primes absent from the actual model order are absent from its canonical
perfect central kernel, by cyclic Sylow transfer. -/
theorem universal_not_dvd_kernel_of_not_dvd_order (hF : 2 < Nat.card F)
    {r : ℕ} [Fact r.Prime] (hr : ¬ r ∣ Nat.card (Model F)) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  apply (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
  intro P
  apply isCyclic_of_card_dvd_prime (p := r)
  rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hr, pow_zero]
  exact one_dvd r

/-- The source prime-field nondefining exclusion reduces to the two small
primes and the remaining primes in the actual model order outside the split
torus. These local inputs remain obligations of final assembly. -/
theorem prime_universal_not_dvd_kernel_of_local_calculations
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (h2 : ¬ 2 ∣ Nat.card (universalProjection (Model F)).ker)
    (h3 : ¬ 3 ∣ Nat.card (universalProjection (Model F)).ker)
    (hnonsplit : ∀ r : ℕ, r.Prime → 3 < r → r ≠ p →
      ¬ r ∣ p - 1 → r ∣ Nat.card (Model F) →
      ¬ r ∣ Nat.card (universalProjection (Model F)).ker)
    {r : ℕ} (hr : r.Prime) (hrp : r ≠ p) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  by_cases htwo : r = 2
  · exact htwo ▸ h2
  by_cases hthree : r = 3
  · exact hthree ▸ h3
  have hrlarge : 3 < r := by have := hr.two_le; omega
  let : Fact r.Prime := ⟨hr⟩
  have hlarge : 2 < Nat.card F := by omega
  by_cases hd : r ∣ p - 1
  · exact OddSplitTorus.universal_not_dvd_kernel_of_split hlarge hrlarge (hF ▸ hd)
  by_cases ho : r ∣ Nat.card (Model F)
  · exact hnonsplit r hr hrlarge hrp hd ho
  · exact universal_not_dvd_kernel_of_not_dvd_order hlarge ho

end Atlas.G2.MultiplierOrdinary.OddNondefining

end
