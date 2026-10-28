module
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowNormalSupplementProduct
/-!
# Specified Sylow intersections in a normal product

A Sylow subgroup intersects a product of normal subgroups in the product
of its intersections. Their joined intersections form a p-subgroup and
contain the specified Sylow restrictions of both factors; the normal
supplement theorem makes that join Sylow in the product. Maximality gives
the equality, retaining the original subgroup embeddings.

The relative form applies inside a normal subgroup. Its consumer is the
paired residual actor selection in Aschbacher--Smith 10.2.1, printed p.743.
-/
public section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem inf_sup_eq_sup_inf_normal (T : Sylow p G) (A B : Subgroup G)
    [A.Normal] [B.Normal] :
    (T : Subgroup G) ⊓ (A ⊔ B) = ((T : Subgroup G) ⊓ A) ⊔ ((T : Subgroup G) ⊓ B) := by
  let J := ((T : Subgroup G) ⊓ A) ⊔ ((T : Subgroup G) ⊓ B)
  have hJT : J ≤ (T : Subgroup G) := sup_le inf_le_left inf_le_left
  have hJN : J ≤ A ⊔ B := sup_le (inf_le_right.trans le_sup_left)
    (inf_le_right.trans le_sup_right)
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal A
  obtain ⟨Q,hQ⟩ := T.exists_sylow_map_eq_inf_of_normal B
  obtain ⟨R,hR⟩ := IsPGroup.exists_sylow_sup_of_normal_sylow_images A B J
    (T.isPGroup'.to_le hJT) hJN P Q (hP ▸ le_sup_left) (hQ ▸ le_sup_right)
  have he : ((T : Subgroup G) ⊓ (A ⊔ B)).subgroupOf (A ⊔ B) =
      (R : Subgroup (A ⊔ B : Subgroup G)) := by
    apply R.is_maximal' ((T.isPGroup'.to_le inf_le_left).comap_subtype)
    intro x hx
    have hxJ := mem_map_of_mem (A ⊔ B).subtype hx
    rw [hR] at hxJ
    exact ⟨hJT hxJ,x.property⟩
  have hh := congrArg (map (A ⊔ B).subtype) he
  rwa [map_subgroupOf_eq_of_le inf_le_right,hR] at hh

theorem inf_sup_eq_sup_inf_relative (T : Sylow p G) (N A B : Subgroup G)
    [N.Normal] (hAN : A ≤ N) (hBN : B ≤ N)
    [(A.subgroupOf N).Normal] [(B.subgroupOf N).Normal] (hAB : A ⊔ B = N) :
    (T : Subgroup G) ⊓ N = ((T : Subgroup G) ⊓ A) ⊔ ((T : Subgroup G) ⊓ B) := by
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal N
  have hh := P.inf_sup_eq_sup_inf_normal (A.subgroupOf N) (B.subgroupOf N)
  have htop : A.subgroupOf N ⊔ B.subgroupOf N = ⊤ := by
    rw [←subgroupOf_sup hAN hBN,hAB,subgroupOf_self]
  rw [htop,inf_top_eq] at hh
  have hm := congrArg (map N.subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ N.subtype_injective,
    Subgroup.map_inf _ _ _ N.subtype_injective,
    hP,map_subgroupOf_eq_of_le hAN,map_subgroupOf_eq_of_le hBN] at hm
  simpa only [inf_assoc,inf_eq_right.mpr hAN,inf_eq_right.mpr hBN] using hm
end Sylow
