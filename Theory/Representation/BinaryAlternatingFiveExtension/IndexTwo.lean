module

public import Theory.Representation.BinaryAlternatingFiveExtension.OverlapFactorizationExtension
public import Mathlib.GroupTheory.Index

/-!
# The ordinary subgroup inside the symmetric affine plane

The literal affine A₅ embedding has image equal to the preimage of A₅ under
the permutation-coordinate map. It is the unique subgroup of index two in
the affine S₅ group containing all translations: passage through the
translation kernel preserves the index, and S₅ has a unique index-two
subgroup. Taking the preimage recovers the given subgroup itself.

This identifies the ordinary subgroup when restricting a marked doubled-plane
comparison in Aschbacher--Smith 13.5.17, printed p.922. In particular the
comparison can retain its same root, translation and overlap markings.
-/

public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension
open Subgroup

/-- The actual ordinary embedding is the preimage of the alternating permutations. -/
theorem symmetricEmbedding_range : symmetricEmbedding.range =
    (alternatingGroup (Fin 5)).comap
      (SemidirectProduct.rightHom : SymmetricModel →* Equiv.Perm (Fin 5)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (symmetricEmbedding y).right ∈ alternatingGroup (Fin 5)
    rw [symmetricEmbedding_right]
    exact y.right.property
  · intro hx
    refine ⟨⟨x.left, ⟨x.right, hx⟩⟩, ?_⟩
    apply SemidirectProduct.ext
    · exact symmetricEmbedding_left _
    · exact symmetricEmbedding_right _

/-- The literal affine A₅ subgroup has index two in the affine S₅ group. -/
theorem symmetricEmbedding_range_index : symmetricEmbedding.range.index = 2 := by
  rw [symmetricEmbedding_range,
    Subgroup.index_comap_of_surjective _ SemidirectProduct.rightHom_surjective]
  exact alternatingGroup.index_eq_two

/-- An index-two subgroup containing the translations is the literal ordinary
affine subgroup. No compatibility of a chosen complement is required. -/
theorem eq_symmetricEmbedding_range_of_index_two (K : Subgroup SymmetricModel)
    (hV : (SemidirectProduct.inl : V →* SymmetricModel).range ≤ K)
    (hindex : K.index = 2) : K = symmetricEmbedding.range := by
  have hk : (SemidirectProduct.rightHom : SymmetricModel →* Equiv.Perm (Fin 5)).ker ≤ K := by
    rwa [← SemidirectProduct.range_inl_eq_ker_rightHom]
  have hq : (K.map (SemidirectProduct.rightHom : SymmetricModel →* Equiv.Perm (Fin 5))).index = 2 :=
    (K.index_map_eq SemidirectProduct.rightHom_surjective hk).trans hindex
  have he := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hq
  rw [symmetricEmbedding_range, ← he, Subgroup.comap_map_eq, sup_eq_left.mpr hk]

end BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension
