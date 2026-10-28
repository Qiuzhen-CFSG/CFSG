module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryModel
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryRealization
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.TwistedCubicTorus.UnitaryEmbedding.Construction
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddCyclotomicSylow.Arithmetic
public import Theory.SpecificGroups.G2.FiniteUniversalCover

/-!
# The twisted cubic torus in the actual G₂ model

`FieldUnits` constructs a cyclic subgroup of the sextic field's units of
full order p² − p + 1, together with its faithful determinant-one regular
action and its invariant nondegenerate trace pairing. `UnitaryModel`
fixes the actual identity-form SU₃ over the quadratic extension.

The theorems below compose two injective homomorphisms: realization of
those units in this SU₃ and realization of this SU₃ in the actual
split-octonion automorphism group. Their image is the required cyclic
subgroup. The checked G₂ order then makes its source Sylow subgroups
cyclic, and perfect-cover transfer excludes the source prime from the
literal kernel of `universalProjection`.

`UnitaryRealization` constructs the first homomorphism by orthonormalizing
the invariant trace pairing. `UnitaryEmbedding.Construction` constructs
the second through an explicit multiplication-preserving comparison of
octonion algebras. Thus `exists_twisted_cubic_torus` has no geometric
premises. It retains the full order p² − p + 1, including prime powers;
the intermediate group is SU₃ itself, with no projective quotient.

Source: Aschbacher–Smith I.1.2–I.1.4, printed pp.407–408, and GLS III
§6.1. This discharges the twisted-torus premise of `OddCyclotomicSylow`;
the complete cyclotomic case split remains with that assembly module.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow

open PerfectCentralCovering TwistedCubicTorus

variable {F : Type*} [Field F] [Finite F]
variable {p : ℕ} [Fact p.Prime]

section UnitaryEmbeddings

variable [CharP F p]

/-- Two faithful, concrete maps realize the twisted cubic torus in G₂.
The construction of these maps is a separate geometric obligation. -/
theorem exists_twisted_cubic_torus_of_unitary_embeddings (hF : Nat.card F = p)
    (ρ : fieldUnits F p →* (standardForm F p).specialSubgroup)
    (hρ : Function.Injective ρ)
    (ι : (standardForm F p).specialSubgroup →* Model F)
    (hι : Function.Injective ι) :
    ∃ C : Subgroup (Model F), IsCyclic C ∧ Nat.card C = p ^ 2 - p + 1 := by
  let f := ι.comp ρ
  let e : fieldUnits F p ≃* f.range := MonoidHom.ofInjective (hι.comp hρ)
  exact ⟨f.range, e.isCyclic.mp inferInstance,
    (Nat.card_congr e.toEquiv).symm.trans (card_fieldUnits F p hF)⟩

/-- Apply the actual torus image to every Sylow subgroup in the twisted branch. -/
theorem sylow_isCyclic_of_twisted_unitary_embeddings (hF : Nat.card F = p)
    (ρ : fieldUnits F p →* (standardForm F p).specialSubgroup)
    (hρ : Function.Injective ρ)
    (ι : (standardForm F p).specialSubgroup →* Model F)
    (hι : Function.Injective ι)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hrp : r ≠ p)
    (hquad : ¬ r ∣ p ^ 2 - 1) (hd : r ∣ p ^ 2 - p + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  obtain ⟨C, hcyclic, hc⟩ :=
    exists_twisted_cubic_torus_of_unitary_embeddings hF ρ hρ ι hι
  let := hcyclic
  exact sylow_isCyclic_of_twisted_cubic_torus hF hr hrp hquad hd C hc Q

/-- The literal universal-cover kernel excludes every source prime in the
twisted branch once the two geometric embeddings have been constructed. -/
theorem universal_not_dvd_kernel_of_twisted_unitary_embeddings
    (hF : Nat.card F = p) (hp : 3 < p)
    (ρ : fieldUnits F p →* (standardForm F p).specialSubgroup)
    (hρ : Function.Injective ρ)
    (ι : (standardForm F p).specialSubgroup →* Model F)
    (hι : Function.Injective ι)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hrp : r ≠ p)
    (hquad : ¬ r ∣ p ^ 2 - 1) (hd : r ∣ p ^ 2 - p + 1) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_twisted_unitary_embeddings hF ρ hρ ι hι hr hrp hquad hd)

end UnitaryEmbeddings

/-- The full twisted cubic torus in the literal split-octonion automorphism
group. Its two faithful embeddings are constructed, and characteristic p
is derived from the cardinality of F. -/
theorem exists_twisted_cubic_torus (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ C : Subgroup (Model F), IsCyclic C ∧ Nat.card C = p ^ 2 - p + 1 := by
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (f := 1) (by
    simpa only [pow_one, Nat.card_eq_fintype_card] using hF)
  obtain ⟨ρ, hρ⟩ := TwistedCubicTorus.exists_unitary_embedding F p hF
  exact exists_twisted_cubic_torus_of_unitary_embeddings hF ρ hρ
    (unitaryEmbedding F p hF hp) (unitaryEmbedding_injective F p hF hp)

/-- The constructed twisted cubic torus contains a full Sylow subgroup at
each source prime; Sylow conjugacy gives cyclicity of every such subgroup. -/
theorem sylow_isCyclic_of_dvd_twisted_cubic (hF : Nat.card F = p) (hp : 3 < p)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hrp : r ≠ p)
    (hquad : ¬ r ∣ p ^ 2 - 1) (hd : r ∣ p ^ 2 - p + 1)
    (Q : Sylow r (Model F)) : IsCyclic Q := by
  obtain ⟨C, hcyclic, hc⟩ := exists_twisted_cubic_torus hF hp
  let := hcyclic
  exact sylow_isCyclic_of_twisted_cubic_torus hF hr hrp hquad hd C hc Q

/-- I.1.2 for the literal universal-cover kernel in the twisted cubic branch,
with the torus construction and both geometric embeddings discharged. -/
theorem universal_not_dvd_kernel_of_dvd_twisted_cubic
    (hF : Nat.card F = p) (hp : 3 < p)
    {r : ℕ} [Fact r.Prime] (hr : 3 < r) (hrp : r ≠ p)
    (hquad : ¬ r ∣ p ^ 2 - 1) (hd : r ∣ p ^ 2 - p + 1) :
    ¬ r ∣ Nat.card (universalProjection (Model F)).ker := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by omega)
  exact (universalCover (Model F)).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_dvd_twisted_cubic hF hp hr hrp hquad hd)

end Atlas.G2.MultiplierOrdinary.OddCyclotomicSylow
