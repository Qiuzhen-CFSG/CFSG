module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.Geometry

/-!
# Involution coboundaries at four-group normalizers in A₆

An involution fixing the marked S₄ pointwise is conjugation by (56).
The outside involutions are double transpositions (ab)(56); explicit even
permutations give their coboundaries. Actual automorphism transport covers
both classes of four-groups and retains the equation for the resulting witness.
A four-group has index two in any dihedral overgroup of order eight, so the
normalizer statement supplies the exact scalar fact needed in the source.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, printed pp.569–570. The uniform S₄
fixed-subgroup premise is explicit and must be discharged by the consumer.
-/

@[expose] public section

open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal.FourNormalizers
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 4096

private theorem standard_pointwise_table (σ : Equiv.Perm (Fin 6))
    (hr : σ * dihedralRotation.val = dihedralRotation.val * σ)
    (hc : σ * threeCyclePerm = threeCyclePerm * σ) : σ = 1 ∨ σ = tailSwap := by
  revert σ
  decide +kernel

theorem pointwise_standard_involution_eq
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ normalizer (standardFour : Set A6), β k = k) :
    β = permutationAction tailSwap := by
  have hn := pointwise_symmetric_involution_mem_natural _
    (normalizer_equiv_symmetric htransS4 standardFour) β hβ2 hβ1 hfix
  obtain ⟨σ, hσ⟩ := hn
  change permutationAction σ = β at hσ
  subst β
  have hr : dihedralRotation ∈ normalizer (standardFour : Set A6) := by
    rw [standard_normalizer_eq_fixed]
    change permutationAction tailSwap dihedralRotation = dihedralRotation
    apply Subtype.ext
    decide +kernel
  have hc : baseThreeCycle ∈ normalizer (standardFour : Set A6) := by
    rw [standard_normalizer_eq_fixed]
    change permutationAction tailSwap baseThreeCycle = baseThreeCycle
    apply Subtype.ext
    decide +kernel
  have hr' := congrArg Subtype.val (hfix dihedralRotation hr)
  have hc' := congrArg Subtype.val (hfix baseThreeCycle hc)
  change σ * dihedralRotation.val * σ⁻¹ = dihedralRotation.val at hr'
  change σ * threeCyclePerm * σ⁻¹ = threeCyclePerm at hc'
  rcases standard_pointwise_table σ (mul_inv_eq_iff_eq_mul.mp hr')
      (mul_inv_eq_iff_eq_mul.mp hc') with h | h
  · exact (hβ1 (by rw [h, map_one])).elim
  · rw [h]

private theorem standard_coboundary_table (f : A6)
    (hn : f.val * tailSwap = tailSwap * f.val) (hf2 : f ^ 2 = 1)
    (hf : ¬ ∃ i : V, standardEmbedding i = f) :
    ∃ k : A6, k * (permutationAction tailSwap k)⁻¹ = f := by
  revert f
  decide +kernel

/-- Every involution outside the four-group in its normalizer is a coboundary
for the nontrivial involution fixing that normalizer pointwise. -/
theorem normalizer_outside_coboundary
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (F : Subgroup A6) [IsKleinFour F]
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ normalizer (F : Set A6), β k = k)
    (f : A6) (hfn : f ∈ normalizer (F : Set A6)) (hf2 : f ^ 2 = 1) (hf : f ∉ F) :
    ∃ k : A6, k * (β k)⁻¹ = f := by
  obtain ⟨α, rfl⟩ := exists_map_standardFour F
  let β' : AutA6 := α⁻¹ * β * α
  have hβ'2 : β' ^ 2 = 1 := by
    change (α⁻¹ * β * α) ^ 2 = 1
    calc
      _ = α⁻¹ * β ^ 2 * α := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hβ2]; group
  have hβ'1 : β' ≠ 1 := by
    intro h
    apply hβ1
    have he := congrArg (fun γ : AutA6 => α * γ * α⁻¹) h
    simpa [β', mul_assoc] using he
  have hfix' : ∀ k ∈ normalizer (standardFour : Set A6), β' k = k := by
    intro k hk
    have hk' : α k ∈ normalizer (standardFour.map α.toMonoidHom : Set A6) := by
      rw [← map_equiv_normalizer_eq]
      exact ⟨k, hk, rfl⟩
    change α.symm (β (α k)) = k
    rw [hfix _ hk', α.symm_apply_apply]
  have hβ'eq := pointwise_standard_involution_eq htransS4 β' hβ'2 hβ'1 hfix'
  have hfn' : α.symm f ∈ normalizer (standardFour : Set A6) := by
    rw [← map_equiv_normalizer_eq, mem_map_equiv] at hfn
    exact hfn
  have hcomm : (α.symm f).val * tailSwap = tailSwap * (α.symm f).val := by
    have hn := mem_normalizer_iff_map_conj_eq.mp hfn'
    rw [← permutationAction_coe] at hn
    exact (natural_stabilizes_standard_iff _).mp hn
  have hf2' : (α.symm f) ^ 2 = 1 := by rw [← map_pow, hf2, map_one]
  have hf' : ¬ ∃ i : V, standardEmbedding i = α.symm f := by
    change α.symm f ∉ standardFour
    rwa [mem_map_equiv] at hf
  obtain ⟨k, hk⟩ := standard_coboundary_table (α.symm f) hcomm hf2' hf'
  rw [← hβ'eq] at hk
  refine ⟨α k, ?_⟩
  have he := congrArg α hk
  simpa [β', map_mul, map_inv] using he

/-- A four-group in a dihedral group of order eight is normal in that group. -/
theorem dihedral_le_four_normalizer (D F : Subgroup A6)
    (hD : Nonempty (D ≃* DihedralGroup 4)) [IsKleinFour F] (hFD : F ≤ D) :
    D ≤ normalizer (F : Set A6) := by
  obtain ⟨e⟩ := hD
  have hcardD : Nat.card D = 8 := (Nat.card_congr e.toEquiv).trans (DihedralGroup.nat_card (n := 4))
  have hcardF : Nat.card (F.subgroupOf D) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFD).toEquiv).trans IsKleinFour.card_four
  have hi : (F.subgroupOf D).index = 2 := by
    have h := (F.subgroupOf D).card_mul_index
    rw [hcardF, hcardD] at h
    omega
  exact (normal_subgroupOf_iff_le_normalizer hFD).mp (normal_of_index_eq_two hi)

/-- Scalar form of the outside-involution fact used in the crossing-square argument. -/
theorem outside_coboundary
    (htransS4 : ∀ σ : Equiv.Perm (Fin 6), σ.IsSwap →
      Nonempty (automorphismFixedSubgroup (permutationAction σ) ≃* Equiv.Perm (Fin 4)))
    (D F : Subgroup A6) (hD : Nonempty (D ≃* DihedralGroup 4)) [IsKleinFour F] (hFD : F ≤ D)
    (β : AutA6) (hβ2 : β ^ 2 = 1) (hβ1 : β ≠ 1)
    (hfix : ∀ k ∈ normalizer (F : Set A6), β k = k)
    (f : A6) (hfD : f ∈ D) (hf2 : f ^ 2 = 1) (hf : f ∉ F) :
    ∃ k : A6, k * (β k)⁻¹ = f :=
  normalizer_outside_coboundary htransS4 F β hβ2 hβ1 hfix f
    (dihedral_le_four_normalizer D F hD hFD hfD) hf2 hf
end AlternatingSix.ShadowLocal.FourNormalizers
