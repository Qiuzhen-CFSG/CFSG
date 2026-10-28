module
public import ABG.ChapterII.Section1.FusionPatterns
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Restriction and transport of automizer indices

If a subgroup `H` contains the ambient normalizer of `U`, computing the
ordinary or outer automizer index of `U` inside `H` gives the ambient value.
Both indices are also invariant under a multiplicative equivalence of ambient
groups. No finiteness assumption is required.

For restriction, the containment of the normalizer puts `U` and its entire
centralizer in `H`. Centralizers and normalizers therefore restrict to their
internal counterparts, and restriction preserves the join `U C(U)` and its
relative index. For transport, an isomorphism maps both centralizers and
normalizers onto their counterparts and preserves joins and relative indices.

These are the index-transfer steps in Alperin–Brauer–Gorenstein, Chapter II,
§2, Proposition 1 (article p.15), when the quaternion central product's whole
normalizer lies in an involution centralizer. The outer denominator retains
both `U` and `C(U)`, exactly as in the source.
-/

namespace ABG
variable {G G' : Type*} [Group G] [Group G']

private theorem centralizer_subgroupOf (H U : Subgroup G) (hUH : U ≤ H) :
    Subgroup.centralizer (U.subgroupOf H : Set H) =
      (Subgroup.centralizer (U : Set G)).subgroupOf H := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (U : Set G)
    intro u hu
    exact congrArg Subtype.val (hx (⟨u, hUH hu⟩ : H) hu)
  · intro hx u hu
    exact Subtype.ext (hx u hu)

private theorem centralizer_map (U : Subgroup G) (e : G ≃* G') :
    Subgroup.centralizer (U.map e.toMonoidHom : Set G') =
      (Subgroup.centralizer (U : Set G)).map e.toMonoidHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    apply Subgroup.mem_map_of_mem
    intro u hu
    apply e.injective
    simpa only [map_mul] using hx (e u) (Subgroup.mem_map_of_mem e.toMonoidHom hu)
  · exact Subgroup.map_centralizer_le_centralizer_image (U : Set G) e.toMonoidHom

/-- A subgroup containing the normalizer computes the same ordinary automizer index. -/
public theorem automizerIndex_subgroupOf (H U : Subgroup G)
    (hNU : Subgroup.normalizer (U : Set G) ≤ H) :
    automizerIndex (U.subgroupOf H) = automizerIndex U := by
  have hUH : U ≤ H := Subgroup.le_normalizer.trans hNU
  unfold automizerIndex
  rw [centralizer_subgroupOf H U hUH, ← Subgroup.subgroupOf_normalizer_eq hUH,
    Subgroup.relIndex_subgroupOf hNU]

/-- A subgroup containing the normalizer computes the same outer automizer index. -/
public theorem outerAutomizerIndex_subgroupOf (H U : Subgroup G)
    (hNU : Subgroup.normalizer (U : Set G) ≤ H) :
    outerAutomizerIndex (U.subgroupOf H) = outerAutomizerIndex U := by
  have hUH : U ≤ H := Subgroup.le_normalizer.trans hNU
  have hCH : Subgroup.centralizer (U : Set G) ≤ H :=
    (Subgroup.centralizer_le_normalizer _).trans hNU
  unfold outerAutomizerIndex
  rw [centralizer_subgroupOf H U hUH, ← Subgroup.subgroupOf_sup hUH hCH,
    ← Subgroup.subgroupOf_normalizer_eq hUH, Subgroup.relIndex_subgroupOf hNU]

/-- An ambient group isomorphism preserves the ordinary automizer index. -/
public theorem automizerIndex_map (U : Subgroup G) (e : G ≃* G') :
    automizerIndex (U.map e.toMonoidHom) = automizerIndex U := by
  unfold automizerIndex
  rw [centralizer_map U e,
    ← Subgroup.map_normalizer_eq_of_bijective U e.bijective,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]

/-- An ambient group isomorphism preserves the outer automizer index. -/
public theorem outerAutomizerIndex_map (U : Subgroup G) (e : G ≃* G') :
    outerAutomizerIndex (U.map e.toMonoidHom) = outerAutomizerIndex U := by
  unfold outerAutomizerIndex
  rw [centralizer_map U e, ← Subgroup.map_sup,
    ← Subgroup.map_normalizer_eq_of_bijective U e.bijective,
    Subgroup.relIndex_map_map_of_injective _ _ e.injective]
end ABG
