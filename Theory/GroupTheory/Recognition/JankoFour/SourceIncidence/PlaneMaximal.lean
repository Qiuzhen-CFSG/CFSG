module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PlaneChart
public import Theory.Mathieu.M22.Properties.HexadMaximal
public import Theory.GroupTheory.NormalSupplementMaximal

/-!
# Maximality and local generation inside the original plane group

The native M₂₂ hexad stabilizer is maximal. In the full design automorphism
group it supplements the normal M₂₂ subgroup, as its index is 77 and the
normal subgroup has index two. Maximality therefore lifts to Aut(M₂₂), then
pulls back along the same original cubic projection to M∩H in H.
The triple-intersection index five shows H∩N escapes M∩H, so these two
literal overlaps generate H.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), opening of §5,
p.599, DOI 10.1007/BF01232280. This is local generation in H; the ambient
generation assertion (6.5)(2) remains separate.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem design_hexad_maximal (B : Finset (Fin 22)) (hB : B ∈ m22Blocks) :
    IsCoatom (MulAction.stabilizer m22DesignAut B) := by
  let A := M22.subgroupOf m22DesignAut
  let J := MulAction.stabilizer m22DesignAut B
  let e : A ≃* M22 := subgroupOfEquivOfLe M22_le_m22DesignAut
  have hm : IsCoatom (J.subgroupOf A) := by
    change IsCoatom ((MulAction.stabilizer M22 B).comap e.toMonoidHom)
    exact isCoatom_comap_of_surjective e.surjective (m22_hexad_stabilizer_isCoatom B hB)
  have hA : A.index = 2 := by
    have hc := A.card_mul_index
    rw [Nat.card_congr e.toEquiv,m22_order,m22DesignAut_order] at hc
    omega
  have hJ : J.index = 77 := by
    have hc := J.card_mul_index
    rw [native_hex_card hB,m22DesignAut_order] at hc
    omega
  have hs : A ⊔ J = ⊤ := by
    apply index_eq_one.mp
    apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 77)
    · rw [←hA]; exact index_dvd_of_le le_sup_left
    · rw [←hJ]; exact index_dvd_of_le le_sup_right
  let : A.Normal := M22_normal_in_m22DesignAut
  exact isCoatom_of_subgroupOf_normal_supplement A J hs hm

namespace LocalData
variable {h : IsTypeJ4 z} (a : LocalData h)

/-- The actual point stabilizer inside the original plane group is maximal.
The native M₂₂ hexad stabilizer remains maximal in Aut(M₂₂), and the original
cubic projection pulls it back to the literal overlap. -/
theorem plane_maximal : IsCoatom (a.P.M.subgroupOf (centralizer z)) := by
  have he : a.P.M.subgroupOf (centralizer z) =
      (MulAction.stabilizer m22DesignAut a.P.hexad).comap a.designProjection := by
    ext n
    exact a.point_plane_overlap n
  rw [he]
  exact isCoatom_comap_of_surjective a.designProjection_surjective
    (design_hexad_maximal a.P.hexad a.P.hexad_mem)

/-- The point and line overlaps generate the original plane group locally.
This is the opening local-generation assertion of §5, not ambient (6.5). -/
theorem plane_flag_generate :
    a.P.M.subgroupOf (centralizer z) ⊔ a.L.G₂.subgroupOf (centralizer z) = ⊤ := by
  apply a.plane_maximal.2
  apply lt_iff_le_not_ge.mpr
  refine ⟨le_sup_left,?_⟩
  intro hh
  have hle : a.L.G₂.subgroupOf (centralizer z) ≤ a.P.M.subgroupOf (centralizer z) :=
    le_sup_right.trans hh
  have he : a.L.G₂ ⊓ centralizer z ≤ a.P.M := by
    intro n hn
    exact hle (show (⟨n,hn.2⟩ : centralizer z) ∈ a.L.G₂.subgroupOf (centralizer z) from hn.1)
  have ht := a.triple_indices.2
  have hi : a.P.M ⊓ a.L.G₂ ⊓ centralizer z = a.L.G₂ ⊓ centralizer z := by
    apply le_antisymm
    · exact inf_le_inf_right _ inf_le_right
    · intro n hn; exact ⟨⟨he hn,hn.1⟩,hn.2⟩
  rw [hi,relIndex_self] at ht
  norm_num at ht
end LocalData
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
