module
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.PlaneCore
public import Theory.GroupTheory.ExtraspecialIntersection

/-!
# Fixed elements in the original radical-core intersection

An element of the extraspecial core has centralizer index at most two.
Restricting to E intersect Q, whose order is 128, leaves at least 64 fixed
elements. This is the size comparison with Todd displacements in the second
paragraph of AS91 (6.4), printed p.602. All intersections are ambient.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceFusion
open LocalGeometry SourceIncidence
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}

/-- Every element of Q fixes at least 64 elements in E intersect Q. -/
lemma planeCore_fixed_card (a : LocalData h) (q : G) (hq : q ∈ ambientCore z) :
    64 ≤ Nat.card (a.P.E ⊓ ambientCore z ⊓ centralizer q : Subgroup G) := by
  let Q := ambientCore z
  let := IsExtraspecial.of_mulEquiv (coreEquivAmbient z) h.extraspecial
  let W := a.P.E.subgroupOf Q
  let u : Q := ⟨q,hq⟩
  let C := Subgroup.centralizer ({u} : Set Q)
  have hi : C.index ≤ 2 := by
    by_cases hu : u ∈ center Q
    · have he : C = ⊤ := by
        apply top_unique
        intro v _
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hu v)
      rw [he,index_top]
      decide
    · exact (ExtraspecialIntersection.centralizer_index_two u hu).le
  have hr : C.relIndex W ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := C) (show W ≤ ⊤ from le_top)
      (by rw [relIndex_top_right]; exact C.index_ne_zero_of_finite)
    rw [relIndex_top_right] at hh
    exact hh.trans hi
  have hW : Nat.card W = 128 := by
    change Nat.card (a.P.E.subgroupOf (ambientCore z)) = 128
    rw [←planeCoreProjection_ker a]
    exact planeCoreProjection_ker_card a
  have hc := (C.subgroupOf W).card_mul_index
  change Nat.card (C.subgroupOf W) * C.relIndex W = Nat.card W at hc
  rw [hW] at hc
  have hb : 64 ≤ Nat.card (C.subgroupOf W) := by nlinarith
  have he : ((C.subgroupOf W).map W.subtype).map Q.subtype =
      a.P.E ⊓ Q ⊓ centralizer q := by
    ext v
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      exact ⟨⟨w.property,w.val.property⟩,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hw))⟩
    · intro hv
      refine ⟨⟨v,hv.1.2⟩,⟨⟨⟨v,hv.1.2⟩,hv.1.1⟩,?_,rfl⟩,rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hv.2))
  rw [←he,card_map_of_injective Q.subtype_injective,
    card_map_of_injective W.subtype_injective]
  exact hb

end Theory.GroupTheory.Recognition.JankoFour.SourceFusion
