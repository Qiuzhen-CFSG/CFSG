module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index

/-!
# Transport of subgroup centralizers and normalizer indices

A group isomorphism carries a subgroup whose centralizer is contained in it
to another subgroup with the same property, and preserves its index in its
normalizer. This lets conjugacy-class calculations establish those local
properties on one representative. If the ambient centralizer is contained in
the subgroup, it is exactly the subgroup's center mapped into the ambient
group; the second theorem states that equality with explicit inclusions.

The first proof uses injectivity and surjectivity to transport commutation,
then Mathlib's normalizer-image and relative-index invariance theorems. The
second proof identifies the two sets elementwise. These elementary transfer
facts support both the four-subgroup and quaternion-subgroup assertions of
Alperin–Brauer–Gorenstein, Chapter II, §1, Lemma 1(ii), article p. 9, in
`refs/latex/alperin-brauer-gorenstein.tex`.
-/

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- Isomorphisms preserve centralizer containment and index two in the normalizer. -/
public theorem local_structure_map (U : Subgroup G) (e : G ≃* H)
    (hC : centralizer (U : Set G) ≤ U) (hN : U.relIndex (normalizer (U : Set G)) = 2) :
    centralizer (U.map e.toMonoidHom : Set H) ≤ U.map e.toMonoidHom ∧
      (U.map e.toMonoidHom).relIndex (normalizer (U.map e.toMonoidHom : Set H)) = 2 := by
  constructor
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    apply mem_map_of_mem
    apply hC
    intro z hz
    apply e.injective
    simpa only [map_mul] using hx (e z) (mem_map_of_mem e.toMonoidHom hz)
  · rw [← map_normalizer_eq_of_bijective U (f := e.toMonoidHom) e.bijective,
      relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective]
    exact hN

/-- A subgroup containing its ambient centralizer has that centralizer equal to its own center. -/
public theorem centralizer_eq_mapped_center_of_le (U : Subgroup G)
    (hC : centralizer (U : Set G) ≤ U) :
    centralizer (U : Set G) = (center U).map U.subtype := by
  apply le_antisymm
  · intro x hx
    refine ⟨⟨x, hC hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hx y y.property
  · rintro x ⟨y, hy, rfl⟩ z hz
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨z, hz⟩)
end Subgroup
