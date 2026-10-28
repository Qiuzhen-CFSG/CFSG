module

public import Glauberman.SuzukiCharacterization.NormalizerCharacterOrbits
public import Glauberman.SuzukiCharacterization.RestrictionPairing
public import Glauberman.SuzukiCharacterization.ColumnIdentities

/-!
# The restriction-degree lower bound

The degree-zero difference of a normalizer orbit representative and a multiple
of the chosen linear character has principal-block column norm `1 + zⱼ²`.
Lemma 3.2 and ordinary orbit orthogonality give this identity without any
additional character-theoretic hypotheses. Each integral entry therefore has
square at most `1 + zⱼ²`; integrality gives the coefficient bound used in (4.6).
Summing over the orbit representatives proves the restriction-degree estimate.

The final theorem combines this estimate with the weighted involution column
identity and its norm `|P|`, obtained from the normal odd complement in the
involution centralizer, to select a character with zero Sylow average.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (3.7), (3.20), and (4.1)–(4.7), pp. 84, 87–90, saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction ModularBlock.RestrictionColumn
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

/-- The exact column norm for a non-first normalizer orbit representative. -/
public theorem NormalizerCharacterOrbitData.restriction_difference_column_norm
    {P : Sylow 2 G} {s : CommutatorSupportData P}
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (j : Fin o.r) (hj : j ≠ o.firstIndex) :
    ∑ i ∈ d.block, Complex.normSq
      (scalarProduct P (restriction d P i) (o.psi j - (o.degree j : ℂ) • s.theta)) =
        1 + (o.degree j : ℝ) ^ 2 := by
  apply CharacterSelection.restriction_column_norm_of_normalizer_pairing
    P d _ (o.difference_isGeneralizedCharacter j) (o.degree j)
  · convert restriction_pairing P h d _ _
      (o.difference_isGeneralizedCharacter j) (o.difference_isGeneralizedCharacter j)
      (o.difference_one j) using 1
    · congr 3
      · exact Subsingleton.elim _ _
      · funext n
        congr 1
        exact Subsingleton.elim _ _
  · convert o.difference_normalizer_pairing h j hj using 1
    congr 3
    · exact Subsingleton.elim _ _
    · funext n
      congr 1
      exact Subsingleton.elim _ _

/-- The integral square bound used to derive equation (4.6). -/
public theorem NormalizerCharacterOrbitData.restriction_multiplicity_difference_sq_le
    {P : Sylow 2 G} {s : CommutatorSupportData P}
    (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (j : Fin o.r) (hj : j ≠ o.firstIndex)
    {i : d.I} (hi : i ∈ d.block) (cⱼ c₁ : ℕ)
    (hcⱼ : scalarProduct P (restriction d P i) (o.psi j) = cⱼ)
    (hc₁ : scalarProduct P (restriction d P i) s.theta = c₁) :
    ((cⱼ : ℤ) - (o.degree j : ℤ) * c₁) ^ 2 ≤ 1 + (o.degree j : ℤ) ^ 2 := by
  exact multiplicity_difference_sq_le_of_norm_sum_le d P _ _ _ hi cⱼ c₁ hcⱼ hc₁
    (o.restriction_difference_column_norm h d j hj).le

namespace CharacterSelection

/-- Equation (4.6) for actual restriction multiplicities, with all orbit and
column inputs discharged from the group hypotheses. -/
public theorem restriction_degree_lower
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P)
    (c₀ c₁ : d.I → ℕ)
    (hc₀ : ∀ i, scalarProduct P (restriction d P i) 1 = c₀ i)
    (hc₁ : ∀ i, scalarProduct P (restriction d P i) s.theta = c₁ i) :
    0 < ((normalizerSylowCore P).index : ℝ) ∧
      ∀ i ∈ d.block,
        (c₀ i : ℝ) + (normalizerSylowCore P).index +
          ((c₁ i : ℝ) - 1) * ((Nat.card P : ℝ) - 1) ≤
            (d.chi i (ConjClasses.mk 1)).re := by
  obtain ⟨o⟩ := h.exists_normalizerCharacterOrbitData P s
  exact o.restriction_degree_lower_of_column_norms h d c₀ c₁ hc₀ hc₁
    (fun j hj => (o.restriction_difference_column_norm h d j hj).le)

/-- Equations (4.1)–(4.7) select a principal-block character with zero Sylow
average, using the constructed commutator support. -/
public theorem exists_zero_sum
    (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G) (s : CommutatorSupportData P) :
    ∃ i ∈ d.block, ∑ x : P, d.chi i (ConjClasses.mk (x : G)) = 0 := by
  obtain ⟨c₀, c₁, hc₀, hc₁⟩ := exists_restriction_multiplicities P d s
  obtain ⟨hq, hlower⟩ := restriction_degree_lower P h d s c₀ c₁ hc₀ hc₁
  exact exists_zero_sum_of_degree_lower P h d s c₀ c₁ hc₀ hc₁
    (normalizerSylowCore P).index hq (fun i hi _ => hlower i hi)

end CharacterSelection
end Glauberman.SuzukiCharacterization
