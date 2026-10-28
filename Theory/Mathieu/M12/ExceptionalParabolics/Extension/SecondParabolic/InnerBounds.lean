module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Seeds
public import Theory.Mathieu.M12.SmallParabolicPair.SylowGeometry

/-!
# Bounds from the marked index-two inner model

The natural four and both parabolics pull back to the existing M₁₂ marks.
Any subgroup has at most two cosets over its intersection with the inner
model. Transporting the known inner orders therefore bounds the outer
second parabolic by 384 and the overlap by 128.
Source: Aschbacher--Smith, F.1.12(I)(13), p.263, and 14.2.21, p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
variable (m : InnerModel)
include m

private theorem embedding_z : m.embedding M12SmallPair.z = z :=
  map_z _ m.embedding_originalA m.embedding_originalB
private theorem embedding_v : m.embedding M12SmallPair.v = v :=
  map_v _ m.embedding_originalA m.embedding_originalB

theorem map_natural : M12SmallPair.natural.map m.embedding = natural := by
  simp only [M12SmallPair.natural, natural, MonoidHom.map_closure, Set.image_insert_eq,
    Set.image_singleton, embedding_z, embedding_v]

theorem comap_firstParabolic : firstParabolic.comap m.embedding = M12SmallPair.firstParabolic := by
  ext x
  change m.embedding x ∈ Subgroup.centralizer ({z} : Set Carrier) ↔
    x ∈ Subgroup.centralizer ({M12SmallPair.z} : Set M12)
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← embedding_z m, ← map_mul, ← map_mul, m.embedding_injective.eq_iff]

theorem comap_secondParabolic :
    secondParabolic.comap m.embedding = M12SmallPair.secondParabolic := by
  rw [secondParabolic, ← map_natural m, Subgroup.comap_normalizer_eq_of_le_range
    (Subgroup.map_le_range _ _), Subgroup.comap_map_eq_self_of_injective m.embedding_injective]
  rfl

theorem comap_overlap : overlap.comap m.embedding = M12SmallPair.sylowCandidate := by
  rw [overlap, Subgroup.comap_inf, comap_firstParabolic, comap_secondParabolic]
  rfl

/-- Every subgroup has at most two cosets over its intersection with the inner model. -/
theorem card_le_twice_comap (K : Subgroup Carrier) :
    Nat.card K ≤ 2 * Nat.card (K.comap m.embedding) := by
  have he : Nat.card (K.comap m.embedding) = Nat.card (inner.subgroupOf K) := by
    rw [← Subgroup.card_map_of_injective (K := K.comap m.embedding) m.embedding_injective,
      Subgroup.map_comap_eq, m.embedding_range]
    rw [← Subgroup.card_map_of_injective (K := inner.subgroupOf K) K.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hi : (inner.subgroupOf K).index ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := inner) (K := K) (L := ⊤) le_top
      (by rw [Subgroup.relIndex_top_right, m.index]; decide)
    rw [Subgroup.relIndex_top_right, m.index, Subgroup.relIndex] at h
    exact h
  rw [he, ← (inner.subgroupOf K).index_mul_card]
  exact Nat.mul_le_mul_right _ hi

theorem card_overlap_le : Nat.card overlap ≤ 128 := by
  have h := card_le_twice_comap m overlap
  rwa [comap_overlap, M12SmallPair.card_sylowCandidate] at h

theorem card_secondParabolic_le : Nat.card secondParabolic ≤ 384 := by
  have h := card_le_twice_comap m secondParabolic
  rwa [comap_secondParabolic, M12SmallPair.card_secondParabolic] at h

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
