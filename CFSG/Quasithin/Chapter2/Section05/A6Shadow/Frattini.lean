module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Involutions
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Normalizer
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ConjugateActions
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.LocalPairs
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore
public import Theory.GroupTheory.PGroup.SylowNormalizerOrbit

/-!
# Assembly of the A₆ Frattini obstruction and involution identities

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemmas
2.5.24–25, printed p.568. An elementary-core orbit for the actual
Q_E = O₂(N_H(E)) contradicts 2.5.10(2): correcting the outside crossing
element by S would enlarge the Sylow normalizer. Thus Φ(S_C) is nontrivial,
and the actual elementary-four centralizer calculation gives tˣ = zK and
z = tzK.

The orbit construction and the full largest-pair classification are explicit
remaining premises. They are not asserted here. This is a conditional
assembly; completion of 2.5.22(1), 2.5.23, and the elementary cases of 2.5.24
must discharge them. The initial interface has no later Frattini or rank-one
conclusion. Source 2.5.10(2) itself is proved in `Frattini.Normalizer` from
2.5.10(1). Right conjugation is explicitly converted to the left action used
by the general Sylow obstruction.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The end of the source Frattini argument. The elementary-core geometry
must supply the displayed orbit for an actual Q_E = O₂(N_H(E)); the pair
classification and 2.5.10(2) then contradict the outside crossing element.
This conditional assembly does not claim to construct that orbit. -/
theorem frattini_ne_of_elementary_orbits (d : EarlierSetup κ G)
    (hpairs : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        largestLocalPairs d.M d.H)
    (hnormalizer : SourceNormalizerCondition d)
    (horbit : IsElementaryAbelian 2 d.SC →
      ∃ E : Subgroup G, E ≤ d.S ⊓ d.K ∧ IsKleinFour E ∧
        ∃ s ∈ d.S,
          rightConjugate d.x (twoCore (d.H ⊓ normalizer (E : Set G))) =
            rightConjugate s (twoCore (d.H ⊓ normalizer (E : Set G)))) :
    frattini d.SC ≠ ⊥ := by
  let : Fact (IsPGroup 2 d.SC) := ⟨d.isTwoGroupS.to_le d.sc_le_s⟩
  intro hphi
  have hel : IsElementaryAbelian 2 d.SC :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  obtain ⟨E, hESK, hE, s, hs, he⟩ := horbit hel
  obtain ⟨P, hP⟩ := hnormalizer _ _ (hpairs E hESK hE)
  have hPe : (P : Subgroup (normalizer
      (twoCore (d.H ⊓ normalizer (E : Set G)) : Set G))).map
        (normalizer (twoCore (d.H ⊓ normalizer (E : Set G)) : Set G)).subtype =
      d.S ⊓ normalizer (twoCore (d.H ⊓ normalizer (E : Set G)) : Set G) := by
    exact (inf_eq_sylow_map P d.isTwoGroupS (hP ▸ inf_le_left)).symm
  have hxinv : d.x⁻¹ ∉ d.S := fun h => d.x_outside (d.S.inv_mem_iff.mp h)
  apply conjugate_ne_of_sylow_normalizer d.T.isPGroup' d.s_le_t P hPe
    ((d.T : Subgroup G).inv_mem d.x_mem) hxinv (d.S.inv_mem hs)
  change rightConjugate d.x _ = rightConjugate s _
  exact he

/-- Conditional assembly of 2.5.24–25 from the three independent earlier
normalizer, largest-pair, and elementary-core geometry inputs. -/
theorem frattini_and_involutions_of_elementary_orbits (d : EarlierSetup κ G)
    (hpairs : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        largestLocalPairs d.M d.H)
    (hchar : ∀ (U L : Subgroup G), (U, L) ∈ localPairsIn (Chapter1.He G) d.M d.H →
      normalizer (twoCore L : Set G) ∈ Chapter1.He G)
    (horbit : IsElementaryAbelian 2 d.SC →
      ∃ E : Subgroup G, E ≤ d.S ⊓ d.K ∧ IsKleinFour E ∧
        ∃ s ∈ d.S,
          rightConjugate d.x (twoCore (d.H ⊓ normalizer (E : Set G))) =
            rightConjugate s (twoCore (d.H ⊓ normalizer (E : Set G)))) :
    frattini d.SC ≠ ⊥ ∧ d.x⁻¹ * d.t * d.x = d.zK ∧ d.z = d.t * d.zK := by
  have hphi := frattini_ne_of_elementary_orbits d hpairs
    (sourceNormalizerCondition_of_characteristic_two d hchar) horbit
  exact ⟨hphi, d.involution_identities_of_frattini_ne hphi⟩

/-!
The preceding theorem is the final local argument with its three source
inputs displayed separately.  The next two bridges package the exact source
clauses used by the section parent: 1.1.3(2) supplies the characteristic-two
centralizer for every conjugate of `z`, and 2.5.12(3) supplies the bijection
between the two inner four-groups and the largest local pairs.  Keeping these
bridges explicit prevents a later setup from being smuggled into the earlier
lemmas.
-/

open ElementaryCore

/-- The genuine 1.1.3(2) input gives the natural-action and commutator
conclusions of 2.5.22(1) for every conjugate of `z` lying in `S`. -/
theorem zConjugateActions_of_centralizer_He
    (d : EarlierSetup κ G)
    (hcentral : ∀ (g : G), g⁻¹ * d.z * g ∈ d.S →
      (centralizer ({d.t} : Set G) ⊓
        centralizer ({g⁻¹ * d.z * g} : Set G)) ∈ Chapter1.He G) :
    ZConjugateActions d := by
  intro g ha
  exact d.conjugate_z_commutator_and_natural g ha (hcentral g ha)

/-- Complete 2.5.22(1), 2.5.23, 2.5.24 and 2.5.25 from the earlier-source
clauses.  The pair correspondence and normalizer characteristic-two premise
are retained as separate inputs, as are the actual centralizer inputs for
the conjugates of `z`; no Frattini or involution conclusion is assumed. -/
theorem source_frattini_and_involutions
    (d : EarlierSetup κ G)
    (hcentral : ∀ (g : G), g⁻¹ * d.z * g ∈ d.S →
      (centralizer ({d.t} : Set G) ⊓
        centralizer ({g⁻¹ * d.z * g} : Set G)) ∈ Chapter1.He G)
    (hcor : d.EarlierPairCorrespondence)
    (hchar : ∀ (U L : Subgroup G),
      (U, L) ∈ localPairsIn (Chapter1.He G) d.M d.H →
        normalizer (twoCore L : Set G) ∈ Chapter1.He G) :
    frattini d.SC ≠ ⊥ ∧ d.x⁻¹ * d.t * d.x = d.zK ∧
      d.z = d.t * d.zK := by
  have hact : ZConjugateActions d := zConjugateActions_of_centralizer_He d hcentral
  have hpairs : ∀ (E : Subgroup G), E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        largestLocalPairs d.M d.H := by
    intro E hE hfour
    rw [← d.normalizerPair_eq E]
    exact d.normalizerPair_largest hcor E hE hfour
  have horbit : IsElementaryAbelian 2 d.SC →
        ∃ E : Subgroup G, E ≤ d.S ⊓ d.K ∧ IsKleinFour E ∧ ∃ s ∈ d.S,
          rightConjugate d.x (twoCore (d.H ⊓ normalizer (E : Set G))) =
            rightConjugate s (twoCore (d.H ⊓ normalizer (E : Set G))) := by
    intro hEA
    exact elementary_normalizer_orbit d hact hEA
  exact frattini_and_involutions_of_elementary_orbits d hpairs hchar
    horbit

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
