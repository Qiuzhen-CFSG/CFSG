module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Models
public import Theory.Alternating.proposition_5_2_7_8

/-!
# Four-group normalizers and element fusion in A₆

The marked four-group normalizer is exactly the fixed subgroup of (56).
Its S₄ identification, conditional on the uniform transposition-fixed-group
identification, transports to every four-group. Explicit conjugators give
transitivity on its three nonidentity elements. The fixed-subgroup D₁₀
theorem excludes exceptional involutions from pointwise centralizers of S₄.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.567–570.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096

theorem map_standard_eq_iff (α : AutA6) :
    standardFour.map α.toMonoidHom = standardFour ↔
      ∀ i : V, ∃ j : V, standardEmbedding j = α (standardEmbedding i) := by
  constructor
  · intro h i
    change α (standardEmbedding i) ∈ standardFour
    rw [← h]
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · intro h
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact h i
    · rw [card_map_of_injective α.injective]

theorem natural_stabilizes_standard_iff (σ : Equiv.Perm (Fin 6)) :
    standardFour.map (permutationAction σ).toMonoidHom = standardFour ↔
      σ * tailSwap = tailSwap * σ := by
  rw [map_standard_eq_iff]
  simp only [Subtype.ext_iff]
  change (∀ i : V, ∃ j : V, (standardEmbedding j).val =
    σ * (standardEmbedding i).val * σ⁻¹) ↔ _
  revert σ
  decide +kernel

theorem standard_normalizer_eq_fixed : normalizer (standardFour : Set A6) =
    automorphismFixedSubgroup (permutationAction tailSwap) := by
  ext g
  rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe g]
  change standardFour.map (permutationAction g.val).toMonoidHom = standardFour ↔ _
  rw [natural_stabilizes_standard_iff]
  change g.val * tailSwap = tailSwap * g.val ↔
    permutationAction tailSwap g = g
  rw [Subtype.ext_iff]
  change _ ↔ tailSwap * g.val * tailSwap⁻¹ = g.val
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem normalizer_equiv_symmetric
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (F : Subgroup A6) [IsKleinFour F] :
    Nonempty (normalizer (F : Set A6) ≃* Equiv.Perm (Fin 4)) := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  obtain ⟨e⟩ := htransS4 tailSwap (by exact ⟨4, 5, by decide, rfl⟩)
  rw [← map_equiv_normalizer_eq]
  exact ⟨((normalizer (standardFour : Set A6)).equivMapOfInjective α.toMonoidHom
    α.injective).symm.trans ((MulEquiv.subgroupCongr standard_normalizer_eq_fixed).trans e)⟩

private theorem standard_transitive_table (i j : V)
    (hi : standardEmbedding i ≠ 1) (hj : standardEmbedding j ≠ 1) :
    ∃ k : A6, k.val * tailSwap = tailSwap * k.val ∧
      k * standardEmbedding i * k⁻¹ = standardEmbedding j := by
  revert i j
  decide +kernel

/-- The normalizer conjugates any nonidentity element of a four-group to any other. -/
theorem four_transitive (F : Subgroup A6) [IsKleinFour F]
    (a : A6) (ha : a ∈ F) (ha1 : a ≠ 1)
    (b : A6) (hb : b ∈ F) (hb1 : b ≠ 1) :
    ∃ k ∈ normalizer (F : Set A6), k * a * k⁻¹ = b := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := ha
  obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hb
  have hi : standardEmbedding i ≠ 1 := by simpa using ha1
  have hj : standardEmbedding j ≠ 1 := by simpa using hb1
  obtain ⟨k, hk, he⟩ := standard_transitive_table i j hi hj
  refine ⟨α k, ?_, ?_⟩
  · rw [← map_equiv_normalizer_eq]
    refine ⟨k, ?_, rfl⟩
    change k ∈ normalizer (standardFour : Set A6)
    rw [mem_normalizer_iff_map_conj_eq, ← permutationAction_coe k]
    exact (natural_stabilizes_standard_iff k.val).mpr hk
  · change α k * α (standardEmbedding i) * (α k)⁻¹ = α (standardEmbedding j)
    simpa only [map_mul, map_inv] using congrArg α he

/-- A genuine involution fixing an S₄ subgroup belongs to the natural S₆ image. -/
theorem pointwise_symmetric_involution_mem_natural (H : Subgroup A6)
    (hH : Nonempty (H ≃* Equiv.Perm (Fin 4)))
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ H, β k = k) : β ∈ natural := by
  by_contra hn
  obtain ⟨eD⟩ := a6_outsideNatural_involution_fixed_equiv_dihedral β
    (orderOf_eq_prime hβ2 hβ1) hn
  obtain ⟨eH⟩ := hH
  have hle : H ≤ automorphismFixedSubgroup β := hfix
  have hd := card_dvd_of_le hle
  rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
    Nat.card_congr eD.toEquiv, DihedralGroup.nat_card] at hd
  norm_num [Nat.factorial] at hd
end AlternatingSix.ShadowLocal.FourNormalizers
