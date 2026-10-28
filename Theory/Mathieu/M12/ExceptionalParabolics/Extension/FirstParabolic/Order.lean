module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.FirstParabolic.Coordinates
public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore

/-!
# Order of the first outer parabolic

The marked embedding identifies the inner intersection of `C(z)` with the
already certified degree-12 centralizer, of order 192. The factor-swapping
lift centralizes `z` and lies outside the inner subgroup. Since the inner
subgroup has index two, its intersection with the first parabolic does too,
so the full first parabolic has order 384.

Source: Aschbacher--Smith, F.1.12(I)(13), printed p.263, and 14.2.21,
printed p.988, `refs/quasithin.pdf`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic

variable (m : InnerModel)
include m

theorem firstParabolic_comap : firstParabolic.comap m.embedding =
    M12SmallPair.firstParabolic := by
  ext x
  change m.embedding x ∈ firstParabolic ↔ x ∈ M12SmallPair.firstParabolic
  simp only [firstParabolic, M12SmallPair.firstParabolic,
    Subgroup.mem_centralizer_singleton_iff]
  rw [← map_z m.embedding m.embedding_originalA m.embedding_originalB,
    ← map_mul, ← map_mul, m.embedding_injective.eq_iff]

theorem firstParabolic_inner_image : M12SmallPair.firstParabolic.map m.embedding =
    inner ⊓ firstParabolic := by
  rw [← firstParabolic_comap m, Subgroup.map_comap_eq, m.embedding_range]

theorem card_inner_firstParabolic : Nat.card (inner ⊓ firstParabolic : Subgroup Carrier) = 192 := by
  rw [← firstParabolic_inner_image m, Subgroup.card_map_of_injective m.embedding_injective]
  exact M12SmallPair.card_firstParabolic

theorem inner_firstParabolic_index : inner.relIndex firstParabolic = 2 := by
  let : inner.Normal := Subgroup.normal_of_index_eq_two m.index
  have hd := inner.relIndex_dvd_index_of_normal firstParabolic
  rw [m.index] at hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · have hle := Subgroup.relIndex_eq_one.mp h
    exact False.elim (nonsplitSwap_not_mem_inner (hle nonsplitSwap_mem_firstParabolic))
  · exact h

theorem card_firstParabolic : Nat.card firstParabolic = 384 := by
  have hc : Nat.card (inner.subgroupOf firstParabolic) = 192 := by
    rw [← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact card_inner_firstParabolic m
  have hi : (inner.subgroupOf firstParabolic).index = 2 := inner_firstParabolic_index m
  have h := (inner.subgroupOf firstParabolic).index_mul_card
  rw [hi,hc] at h
  exact h.symm

theorem quaternionCore_le_firstParabolic : quaternionCore ≤ firstParabolic := by
  rw [quaternionCore_eq_map m]
  exact (Subgroup.map_mono M12SmallPair.core_le_firstParabolic).trans
    ((firstParabolic_inner_image m) ▸ inf_le_right)

end Sporadic.Mathieu.M12ExceptionalExtension.FirstParabolic
