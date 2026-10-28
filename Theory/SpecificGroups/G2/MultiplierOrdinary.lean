module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.SpecificGroups.G2.MultiplierOrdinary.UnipotentSection
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddNondefining
public import Theory.SpecificGroups.G2.MultiplierOrdinary.NondefiningPrimes
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations

/-!
# Triviality of the ordinary G₂ universal-cover kernels

For each source family, the six actual positive-root groups lift compatibly
through the canonical universal projection. Their proved multiplication law
splits the literal unipotent subgroup, excluding the defining prime by
transfer. The concrete torus and Sylow calculations exclude every other
prime. Finiteness of the universal cover then makes its kernel trivial.

The unconditional conclusions apply to G₂(2^n), n ≥ 3, and G₂(p), p an odd
prime greater than three, on the actual split-octonion model and the literal
free-central-extension projection. The earlier conditional assembly remains
available, and its premises are discharged below. Orders three and four
have exceptional multipliers and are excluded from these conclusions.
The G₂(2)' endpoint belongs to the separate PSU₃(3) comparison.

Source: Aschbacher–Smith A.2.2–A.2.4, printed p.33 (PDF p.44),
I.1.3–I.1.4, printed pp.407–408 (PDF pp.418–419), and GLS III §6.1.
-/

public section

namespace Atlas.G2.MultiplierOrdinary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- The source even-field range supplies six additive sections of the
literal canonical projection, without a multiplier assumption. -/
theorem even_universal_root_sections {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n) :
    Nonempty (RootSections (universalProjection (Model F))) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hlarge : 4 < Nat.card F := by
    have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact even_root_sections hlarge (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- The source odd-prime range supplies the same actual additive sections.
This asserts no compatibility between distinct positive roots. -/
theorem prime_universal_root_sections {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    Nonempty (RootSections (universalProjection (Model F))) := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact prime_root_sections hF (by omega) (universalProjection (Model F))
    (universalProjection_surjective _) (universalProjection_ker_le_center _)

/-- Conditional assembly on the canonical cover, retaining the independent
positive-root multiplication law and nondefining-prime exclusions as inputs. -/
theorem universalProjection_ker_eq_bot_of_positive_relations
    {p : ℕ} [Fact p.Prime] [CharP F p] (hF : 2 < Nat.card F)
    (L : RootSections (universalProjection (Model F))) (hL : L.ProductCompatible)
    (hother : ∀ r : ℕ, r.Prime → r ≠ p →
      ¬ r ∣ Nat.card (universalProjection (Model F)).ker) :
    (universalProjection (Model F)).ker = ⊥ := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect hF
  have hdef : ¬ p ∣ Nat.card (universalProjection (Model F)).ker :=
    not_dvd_kernel_of_positive_relations (universalCover (Model F)) L hL
  apply Subgroup.card_eq_one.mp
  by_contra h
  obtain ⟨r, hr, hdiv⟩ := Nat.exists_prime_and_dvd h
  by_cases heq : r = p
  · exact hdef (heq ▸ hdiv)
  · exact hother r hr heq hdiv

/-- The literal canonical universal-cover kernel is trivial in characteristic
two with more than four field elements. Both the positive-root multiplication
law and every nondefining-prime exclusion are discharged. -/
theorem even_universalProjection_ker_eq_bot [CharP F 2] (hF : 4 < Nat.card F) :
    (universalProjection (Model F)).ker = ⊥ := by
  obtain ⟨L, hL⟩ := even_universal_compatible_sections hF
  exact universalProjection_ker_eq_bot_of_positive_relations (p := 2) (by omega) L hL
    (fun _ hr hr2 => NondefiningPrimes.even_not_dvd_card_universal_kernel hF hr hr2)

/-- The source family G₂(2^n), n ≥ 3, has trivial Schur multiplier.
Characteristic two is derived from the field order, so no extra model or
characteristic hypothesis is needed by the multiplier-table consumer. -/
theorem even_universalProjection_ker_eq_bot_of_card_pow
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n) :
    (universalProjection (Model F)).ker = ⊥ := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hpow : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  exact even_universalProjection_ker_eq_bot (by omega)

/-- The source family G₂(p), p prime and p > 3, has trivial Schur multiplier.
This combines the actual compatible root lifts with all nondefining-prime
exclusions, including the nondefining primes two and three. -/
theorem prime_universalProjection_ker_eq_bot {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp : 3 < p) :
    (universalProjection (Model F)).ker = ⊥ := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨L, hL⟩ := prime_universal_compatible_sections hF hp
  exact universalProjection_ker_eq_bot_of_positive_relations (p := p) (by omega) L hL
    (fun _ hr hrp => NondefiningPrimes.prime_not_dvd_card_universal_kernel hF hp hr hrp)

end Atlas.G2.MultiplierOrdinary

end
