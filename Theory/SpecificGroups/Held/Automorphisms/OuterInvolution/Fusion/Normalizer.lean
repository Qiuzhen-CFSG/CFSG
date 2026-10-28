module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.GraphCardBound
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Reduction

/-!+# The two cosets of Held in its full permutation normalizer

Orbital preservation and the graph bound give index at most two. The checked
outer representative excludes index one. Thus every element of the full
normalizer is an inner element or an inner element times the representative.
This also identifies the generated extension with the full normalizer and
gives its exact order, without realizing abstract automorphisms.

Source: GLS3 Table 5.3p, interpreted on pp.260–261; the fixed ATLAS
degree-2058 representation and the independently checked orbital certificates.
-/

public section
namespace Held.OuterInvolution.Fusion
open Subgroup LocalPairs LocalPairs.SylowGeometry

/-- The graph's certified four-point base is also a base for the full normalizer.
Finite identities between actual normalizer elements need only these four images. -/
theorem normalizer_ext_four (x y : PermutationNormalizer)
    (h : ∀ i : Fin 4, x.val ⟨i.val, by omega⟩ = y.val ⟨i.val, by omega⟩) : x = y := by
  apply Subtype.ext
  have he : y.val⁻¹ * x.val = 1 := by
    apply NormalizerGraph.CardBound.four_fixed_eq_one
    · exact NormalizerGraph.Orbital.normalizer_le_preservingGroup (y⁻¹ * x).property
    · intro z hz
      have he := h ⟨z.val, hz⟩
      change x.val z = y.val z at he
      change y.val.symm (x.val z) = z
      rw [he, Equiv.symm_apply_apply]
  exact (inv_mul_eq_one.mp he).symm

theorem normalizerQuotient_card_le_two :
    Nat.card PermutationNormalizerQuotient ≤ 2 :=
  permutationNormalizerQuotient_card_le_two_of_graph
    NormalizerGraph.Orbital.normalizer_le_preservingGroup
    NormalizerGraph.card_preservingGroup_le

theorem representative_not_mem_inner : representative ∉ innerSubgroup := by
  intro h
  exact action_not_inner ((normalizer_action_inner_iff representative).mpr h)

theorem inner_index : innerSubgroup.index = 2 := by
  have hle := normalizerQuotient_card_le_two
  change innerSubgroup.index ≤ 2 at hle
  have hpos := innerSubgroup.index_ne_zero_of_finite
  have hne : innerSubgroup.index ≠ 1 := by
    intro h
    exact representative_not_mem_inner ((index_eq_one.mp h) ▸ mem_top _)
  omega

/-- Any specified element outside Held represents the other coset. -/
theorem exists_inner_mul (t n : PermutationNormalizer) (ht : t ∉ innerSubgroup)
    (hn : n ∉ innerSubgroup) : ∃ g : He, innerEmbedding g * t = n := by
  have hm : n * t⁻¹ ∈ innerSubgroup :=
    (mul_mem_iff_of_index_two inner_index).mpr
      (iff_of_false hn (fun h => ht (inv_mem_iff.mp h)))
  let g : He := ⟨(n * t⁻¹).val, hm⟩
  refine ⟨g, ?_⟩
  change (n * t⁻¹) * t = n
  simp only [inv_mul_cancel_right]

/-- This is a decomposition of the full normalizer, not just an exhibited extension. -/
theorem normalizer_cases (n : PermutationNormalizer) :
    (∃ g : He, innerEmbedding g = n) ∨
      (∃ g : He, innerEmbedding g * representative = n) := by
  by_cases hn : n ∈ innerSubgroup
  · exact Or.inl ⟨⟨n.val, hn⟩, rfl⟩
  · exact Or.inr (exists_inner_mul representative n representative_not_mem_inner hn)

/-- The generated concrete extension exhausts the full permutation normalizer. -/
theorem generated_extension_eq_normalizer :
    permutationGroup ⊔ zpowers (representative : Equiv.Perm (Fin 2058)) =
      normalizer (permutationGroup : Set (Equiv.Perm (Fin 2058))) := by
  apply le_antisymm
  · exact sup_le permutationGroup.le_normalizer
      (zpowers_le.mpr representative.property)
  · intro n hn
    rcases normalizer_cases ⟨n, hn⟩ with ⟨g, hg⟩ | ⟨g, hg⟩
    · have hv : representation g = n := congrArg Subtype.val hg
      rw [← hv]
      exact mem_sup_left g.property
    · have hv : representation g * representative.val = n := congrArg Subtype.val hg
      rw [← hv]
      exact mul_mem (mem_sup_left g.property) (mem_sup_right (mem_zpowers _))

theorem normalizer_card : Nat.card PermutationNormalizer = 8060774400 := by
  have hupper : Nat.card PermutationNormalizer ≤ 8060774400 :=
    (Nat.card_le_card_of_injective
      (inclusion NormalizerGraph.Orbital.normalizer_le_preservingGroup)
      (inclusion_injective _)).trans NormalizerGraph.card_preservingGroup_le
  have hcard : Nat.card innerSubgroup = Nat.card He :=
    Nat.card_congr (subgroupOfEquivOfLe permutationGroup.le_normalizer).toEquiv
  have hmul := innerSubgroup.card_mul_index
  rw [inner_index, hcard] at hmul
  have hlow := NormalizerBounds.card_lower_bound
  omega

end Held.OuterInvolution.Fusion
