module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.NondefiningPrimes
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.Assembly

/-!
# Applying both ordinary G₂ nondefining-prime exclusions

The imported even-field application and the odd-prime application below
discharge every nondefining-prime premise of the ordinary-kernel assembly.
Both use the literal canonical projection and its actual root sections.
Only the independent multiplication law between positive-root sections
remains explicit. Thus this module does not assert the full trivial-multiplier
entry of Aschbacher–Smith I.1.3–I.1.4, printed pp.407–408 (PDF pp.418–419).
-/

public section

namespace Atlas.G2.MultiplierOrdinary

open PerfectCentralCovering

variable {F : Type*} [Field F] [Finite F]

/-- In the ordinary odd-prime source range, the positive-root multiplication
law suffices for kernel vanishing: every nondefining prime is excluded. -/
theorem prime_universalProjection_ker_eq_bot_of_positive_relations
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) (hp : 3 < p)
    (L : RootSections (universalProjection (Model F))) (hL : L.ProductCompatible) :
    (universalProjection (Model F)).ker = ⊥ := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  exact universalProjection_ker_eq_bot_of_positive_relations (p := p) (by omega) L hL
    (fun _ hr hrp => NondefiningPrimes.prime_not_dvd_card_universal_kernel hF hp hr hrp)

end Atlas.G2.MultiplierOrdinary

end
