module

public import Glauberman.SuzukiCharacterization.CharacterSelectionArithmetic
public import Glauberman.SuzukiCharacterization.NormalizerBasics
public import Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitPairing
public import Theory.Character.ModularBlock.RestrictionColumnBounds

/-!
# From restriction-column norms to the restriction-degree estimate

The restriction decomposes into its principal term and normalizer orbits of
nonprincipal irreducibles. Their degrees have squared mass (|P|-1)/q.
A column norm bound for ψⱼ-zⱼψ₁ bounds each integral coefficient difference;
the arithmetic lemma then yields equation (4.6). This module keeps the orbit
decomposition and column norm identities explicit. Their unconditional
construction is the remaining character-theoretic input.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (3.7), (3.13), and (4.6), pp. 84–89, saved in
`refs/original/n-group-global/odd-core-rank-two-source/`.
-/

open scoped BigOperators
open ModularBlock.PrincipalBlockConstruction ModularBlock.RestrictionColumn
noncomputable section
attribute [local instance] Fintype.ofFinite
namespace Glauberman.SuzukiCharacterization.CharacterSelection

/-- Equation (3.7), in the exact real norm form needed for (4.6).
The two inputs separate the modular column-pairing theorem (Lemma 3.2)
from ordinary normalizer-orbit orthogonality (Lemma 3.3). In the application
`δ = ψⱼ - zⱼ ψ₁`, so that the ordinary self-pairing is `1 + zⱼ²`. -/
public theorem restriction_column_norm_of_normalizer_pairing
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (d : PrincipalCongruenceBlockData G)
    (δ : ClassFunction P) (hδ : IsGeneralizedCharacter δ) (z : ℕ)
    (hpair : ∑ i ∈ d.block,
      (coefficient d P δ hδ i : ℂ) * (coefficient d P δ hδ i : ℂ) =
        (Nat.card (normalizerSylowCore P) : ℂ)⁻¹ *
          ∑ n : Subgroup.normalizer (P : Set G),
            scalarProduct P
              (fun x => δ ((P : Subgroup G).normalizerMonoidHom n x)) δ)
    (horbit : (∑ n : Subgroup.normalizer (P : Set G),
        scalarProduct P
          (fun x => δ ((P : Subgroup G).normalizerMonoidHom n x)) δ) =
      (Nat.card (normalizerSylowCore P) : ℂ) * (1 + (z : ℂ) ^ 2)) :
    ∑ i ∈ d.block, Complex.normSq (scalarProduct P (restriction d P i) δ) =
      1 + (z : ℝ) ^ 2 := by
  apply norm_sum_eq_of_coefficient_self_pairing d P δ hδ
  rw [hpair, horbit,
    inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr
      (Nat.card_pos (α := normalizerSylowCore P)).ne')]
  push_cast
  rfl

/-- Equation (4.6) from actual restriction multiplicities and column norms.
The conclusion holds for every block row, so in particular it supplies
`hlower` in `exists_zero_sum_of_column_identities`. -/
public theorem restriction_degree_lower_of_column_norms
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P)
    (d : PrincipalCongruenceBlockData G)
    {ι : Type*} [DecidableEq ι] (J : Finset ι) (j₁ : ι) (hj₁ : j₁ ∈ J)
    (ψ : ι → ClassFunction P) (z : ι → ℕ)
    (c : d.I → ι → ℕ) (c₀ c₁ : d.I → ℕ)
    (hc : ∀ i ∈ d.block, ∀ j ∈ J,
      scalarProduct P (restriction d P i) (ψ j) = c i j)
    (hc₁ : ∀ i ∈ d.block, scalarProduct P (restriction d P i) (ψ j₁) = c₁ i)
    (hz : ∀ j ∈ J, 0 < z j) (hz₁ : z j₁ = 1)
    (hdegree : ∀ i ∈ d.block,
      (d.chi i (ConjClasses.mk 1)).re = (c₀ i : ℝ) +
        (normalizerSylowCore P).index * ∑ j ∈ J, (c i j : ℝ) * z j)
    (hmass : (Nat.card P : ℝ) - 1 =
      (normalizerSylowCore P).index * ∑ j ∈ J, (z j : ℝ) ^ 2)
    (hcolumn : ∀ j ∈ J, j ≠ j₁ →
      ∑ i ∈ d.block, Complex.normSq
        (scalarProduct P (restriction d P i) (ψ j - (z j : ℂ) • ψ j₁)) ≤
          1 + (z j : ℝ) ^ 2) :
    0 < ((normalizerSylowCore P).index : ℝ) ∧
      ∀ i ∈ d.block,
        (c₀ i : ℝ) + (normalizerSylowCore P).index +
          ((c₁ i : ℝ) - 1) * ((Nat.card P : ℝ) - 1) ≤
            (d.chi i (ConjClasses.mk 1)).re := by
  have hq : 0 < ((normalizerSylowCore P).index : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (h.one_lt_normalizerSylowCore_index P))
  refine ⟨hq, ?_⟩
  intro i hi
  have he : c i j₁ = c₁ i := by
    exact_mod_cast (hc i hi j₁ hj₁).symm.trans (hc₁ i hi)
  have hl := degree_lower_of_column_sq_bounds J j₁ hj₁ z (c i) (c₀ i)
    (normalizerSylowCore P).index ((Nat.card P : ℝ) - 1)
    (d.chi i (ConjClasses.mk 1)).re hq.le hz hz₁ (hdegree i hi) hmass
    (fun j hj hne => multiplicity_difference_sq_le_of_norm_sum_le d P
      (ψ j) (ψ j₁) (z j) hi (c i j) (c i j₁)
      (hc i hi j hj) (hc i hi j₁ hj₁) (hcolumn j hj hne))
  simpa only [he] using hl

end Glauberman.SuzukiCharacterization.CharacterSelection
