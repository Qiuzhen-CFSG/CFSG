module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.Arithmetic
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.CubicTorus
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# Cyclotomic Sylow subgroups and the ordinary G₂ multiplier

For a prime field of order p > 3, the checked model order places every
prime r > 3 dividing |G₂(p)| and missing p(p² − 1) in p² + p + 1 or
p² − p + 1. The cubic norm-one torus and the twisted cubic torus are
actual cyclic subgroups of these full orders in the octonion model.
Their indices are prime to r in the corresponding branches, so Sylow
conjugacy proves that every Sylow r-subgroup is cyclic. Cyclic-Sylow
transfer then excludes r from the literal kernel of the canonical
universal cover.

The conditional assembly interfaces are retained. The final two theorems
discharge their geometric premise with the constructed twisted torus.

Source: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408 (PDF pp.418–419),
and GLS III §6.1. All covers below use the actual octonion G₂ model.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- The cubic norm-one torus contains a full Sylow subgroup, and conjugacy
transports its cyclicity to every Sylow subgroup at the same prime. -/
theorem sylow_isCyclic_of_dvd_cubic
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (hd : r ∣ p ^ 2 + p + 1) (Q : Sylow r (Model F)) : IsCyclic Q := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := 1) (by
    simpa only [pow_one, Nat.card_eq_fintype_card] using hF)
  obtain ⟨C, hcyclic, hc⟩ := exists_cubic_torus F p
  let := hcyclic
  exact sylow_isCyclic_of_cubic_torus hF hr hrp hquad hd C (by simpa only [hF] using hc) Q

/-- I.1.2 applied to the actual canonical cover, for the cubic cyclotomic branch. -/
theorem universal_not_dvd_kernel_of_dvd_cubic
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (hd : r ∣ p ^ 2 + p + 1) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_cubic hF hr hrp hquad hd)

/-- Conditional assembly from an actual cyclic subgroup of order p² − p + 1.
The unconditional theorem below supplies the constructed twisted torus. -/
theorem sylow_isCyclic_of_twisted_torus_exists
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (htwisted : ∃ C : Subgroup (Model F), IsCyclic C ∧ Nat.card C = p ^ 2 - p + 1)
    (horder : r ∣ Nat.card (Model F)) (Q : Sylow r (Model F)) : IsCyclic Q := by
  rcases cyclotomic_alternatives hF hrp hquad horder with h3 | h6
  · exact sylow_isCyclic_of_dvd_cubic hF hr hrp hquad h3 Q
  · obtain ⟨C, hcyclic, hc⟩ := htwisted
    let := hcyclic
    exact sylow_isCyclic_of_twisted_cubic_torus hF hr hrp hquad h6 C hc Q

/-- The literal universal-kernel consumer of the two torus branches,
with the twisted cubic torus supplied explicitly. -/
theorem universal_not_dvd_kernel_of_twisted_torus_exists
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (htwisted : ∃ C : Subgroup (Model F), IsCyclic C ∧ Nat.card C = p ^ 2 - p + 1)
    (horder : r ∣ Nat.card (Model F)) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_twisted_torus_exists hF hr hrp hquad htwisted horder)

/-- Every Sylow subgroup at a source cyclotomic prime is cyclic. Both
torus constructions are discharged in the literal octonion model. -/
theorem sylow_isCyclic
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (horder : r ∣ Nat.card (Model F)) (Q : Sylow r (Model F)) : IsCyclic Q :=
  sylow_isCyclic_of_twisted_torus_exists hF hr hrp hquad
    (exists_twisted_cubic_torus hF hp) horder Q

/-- I.1.2 excludes every source cyclotomic prime from the literal canonical
universal-cover kernel, with no torus or cyclicity premise left over. -/
theorem universal_not_dvd_kernel
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (hr : 3 < r) (hrp : r ≠ p) (hquad : ¬ r ∣ p ^ 2 - 1)
    (horder : r ∣ Nat.card (Model F)) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic hF hp hr hrp hquad horder)

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow
