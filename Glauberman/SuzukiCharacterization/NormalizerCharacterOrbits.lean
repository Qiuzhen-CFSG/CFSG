module

public import Glauberman.SuzukiCharacterization.NormalizerCharacterAction
public import Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitSums
public import Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitPairing

/-!
# Ordinary character orbits in the Suzuki characterization

This interface re-exports the free normalizer quotient action and its pointed
finite family of orbit representatives, their squared-degree mass, the actual
restriction multiplicities, and the ordinary pairing of difference characters.
The stabilizer calculation uses Brauer permutation and the Frobenius centralizer
theorem; a section of the finite orbit quotient chooses the family with first
character equal to the prescribed theta. Reindexing the irreducible character
expansion gives the restriction degree formula.

`exists_normalizerCharacterOrbitData_with_multiplicities` assembles the ordinary
data from the group hypotheses. The methods `degree_sq_mass`,
`degree_sq_mass_real`, `difference_isGeneralizedCharacter`, `difference_one`,
and `difference_normalizer_pairing` expose its numerical and pairing properties.
The final adapter discharges every ordinary input of the restriction-degree
bound, keeping its modular column-norm hypothesis explicit.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968), Lemma 3.3
and equations (3.6), (3.13), pp. 84–86, saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction ModularBlock.RestrictionColumn
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

/-- Construct the pointed orbit family and its actual restriction multiplicities.
The remaining degree and difference-character identities are methods of `o`. -/
public theorem Hypotheses.exists_normalizerCharacterOrbitData_with_multiplicities
    (P : Sylow 2 G) (h : Hypotheses P) (s : CommutatorSupportData P)
    (d : PrincipalCongruenceBlockData G) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (restriction d P i) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (restriction d P i) s.theta = c₁ i) :
    ∃ (o : NormalizerCharacterOrbitData P s) (c : d.I → Fin o.r → ℕ),
      (∀ i j, scalarProduct P (restriction d P i) (o.psi j) = c i j) ∧
      (∀ i, c i o.firstIndex = c₁ i) ∧
      (∀ i, (d.chi i (ConjClasses.mk 1)).re = (c₀ i : ℝ) +
        (normalizerSylowCore P).index *
          ∑ j : Fin o.r, (c i j : ℝ) * o.degree j) := by
  obtain ⟨o⟩ := h.exists_normalizerCharacterOrbitData P s
  exact ⟨o, o.exists_restriction_orbit_multiplicities d c₀ c₁ hc₀ hc₁⟩

/-- Apply the restriction-degree bound to the constructed ordinary orbit data.
Only the modular column-norm bound remains an external input. -/
public theorem NormalizerCharacterOrbitData.restriction_degree_lower_of_column_norms
    {P : Sylow 2 G} {s : CommutatorSupportData P}
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (restriction d P i) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (restriction d P i) s.theta = c₁ i)
    (hcolumn : ∀ j : Fin o.r, j ≠ o.firstIndex →
      ∑ i ∈ d.block, Complex.normSq
        (scalarProduct P (restriction d P i) (o.psi j - (o.degree j : ℂ) • s.theta)) ≤
          1 + (o.degree j : ℝ) ^ 2) :
    0 < ((normalizerSylowCore P).index : ℝ) ∧
      ∀ i ∈ d.block,
        (c₀ i : ℝ) + (normalizerSylowCore P).index +
          ((c₁ i : ℝ) - 1) * ((Nat.card P : ℝ) - 1) ≤
            (d.chi i (ConjClasses.mk 1)).re := by
  obtain ⟨c, hc, _, hdegree⟩ :=
    o.exists_restriction_orbit_multiplicities d c₀ c₁ hc₀ hc₁
  apply CharacterSelection.restriction_degree_lower_of_column_norms P h d
    Finset.univ o.firstIndex (Finset.mem_univ _) o.psi o.degree c c₀ c₁
  · exact fun i _ j _ => hc i j
  · simpa only [o.psi_first] using fun i (_ : i ∈ d.block) => hc₁ i
  · exact fun j _ => o.degree_pos j
  · exact o.degree_first
  · exact fun i _ => hdegree i
  · exact o.degree_sq_mass_real
  · simpa only [o.psi_first] using fun j (_ : j ∈ Finset.univ) => hcolumn j

end Glauberman.SuzukiCharacterization
