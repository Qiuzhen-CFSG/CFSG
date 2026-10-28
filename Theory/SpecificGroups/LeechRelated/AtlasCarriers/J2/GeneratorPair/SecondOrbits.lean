module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.NormalForms
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.OrbitRepresentatives
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.Coverage
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.SecondOrbits.FiniteCheck

/-!
# The two centralizer orbits of J₂ generator partners

Every element satisfying the pair profile with `a` is conjugate to `b` or
`b⁻¹` by an element of the actual carrier centralizing `a`. Coverage by the
four-level normal forms and the exhaustive finite classification identify
each such element with a supplied partner. The explicit centralizing words
then provide the required conjugator inside J₂.

Source: the retained ATLAS `J2G1-p100B0` permutations and GLS3, Table 5.3g.
The three equality tests already suffice in the witness search, but the
formal interface preserves the complete published `PairProfile`.
-/

public section
namespace Sporadic.LeechRelated.J2.GeneratorPair
open SecondOrbitCertificate

/-- Transport of the exact pair profile to the faithful permutation action. -/
theorem pairProfile_iff_ambient (y : Carrier) :
    PairProfile a y ↔ AmbientProfile (inclusion y) := by
  constructor
  · rintro ⟨_, hy, h7, h12, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [map_pow, map_one] using congrArg inclusion hy
    · simpa only [map_pow, map_mul, map_one, a_inclusion] using congrArg inclusion h7
    · simpa only [map_pow, map_mul, map_inv, map_one, a_inclusion] using
        congrArg inclusion h12
    · intro heq
      apply h4
      apply inclusion_injective
      simpa only [map_pow, map_mul, map_inv, map_one, a_inclusion] using heq
  · rintro ⟨hy, h7, h12, h4⟩
    refine ⟨a_pow_two, ?_, ?_, ?_, ?_⟩
    · apply inclusion_injective
      simpa only [map_pow, map_one] using hy
    · apply inclusion_injective
      simpa only [map_pow, map_mul, map_one, a_inclusion] using h7
    · apply inclusion_injective
      simpa only [map_pow, map_mul, map_inv, map_one, a_inclusion] using h12
    · intro heq
      apply h4
      simpa only [map_pow, map_mul, map_inv, map_one, a_inclusion] using
        congrArg inclusion heq

set_option maxRecDepth 100000 in
/-- The inverse standard generator satisfies the same complete word tests. -/
theorem pair_profile_inverse : PairProfile a b⁻¹ := by
  apply (pairProfile_iff_ambient _).mpr
  rw [map_inv, b_inclusion]
  unfold AmbientProfile
  decide +kernel

/-- Both supplied partner families pass the original tests. -/
theorem pair_profile_partner (i : Fin 240) (inverse : Bool) :
    PairProfile a (partner i inverse) := by
  have h : PairProfile a (if inverse then b⁻¹ else b) := by
    cases inverse
    · exact pair_profile
    · exact pair_profile_inverse
  simpa only [conjugator_centralizes, partner] using h.map (MulAut.conj (conjugator i))

/-- Assembly of a normal-form cover and a finite partner classification. -/
theorem second_generator_orbits_of_finite_certificates
    (cover : ∀ y : Carrier, ∃ i : Index, inclusion y = normalForm i)
    (classify : ∀ i : Index, AmbientProfile (normalForm i) →
      ∃ j : Fin 240, ∃ inverse : Bool, normalForm i = partnerTable j inverse)
    (y : Carrier) (h : PairProfile a y) :
    ∃ c : Carrier, MulAut.conj c a = a ∧
      (y = MulAut.conj c b ∨ y = MulAut.conj c b⁻¹) := by
  obtain ⟨i, hi⟩ := cover y
  have hp := (pairProfile_iff_ambient y).mp h
  rw [hi] at hp
  obtain ⟨j, inverse, hj⟩ := classify i hp
  have hy : y = partner j inverse := by
    apply inclusion_injective
    rw [hi, hj, partner_inclusion]
  rw [hy]
  exact partner_has_orbit j inverse

/-- Every partner of `a` lies in the centralizer orbit of `b` or `b⁻¹`,
with a conjugator in the exact ATLAS-generated J₂ carrier. -/
theorem second_generator_orbits (y : Carrier) (h : PairProfile a y) :
    ∃ c : Carrier, MulAut.conj c a = a ∧
      (y = MulAut.conj c b ∨ y = MulAut.conj c b⁻¹) :=
  second_generator_orbits_of_finite_certificates
    normalForm_cover normalForm_classification y h

end Sporadic.LeechRelated.J2.GeneratorPair
