module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRowGeometry
/-!
# The characteristic rectangle in the source point–plane intersection

In the literal intersection `I = N_G(row) ∩ N_G(threeSpace)`, every normal
elementary subgroup of order at least 64 is the marked three-space rectangle.
Indeed it lies in the original Sylow, whose elementary census gives the two
rectangles. The other rectangle cannot be normal: the two distinct maximal
row parabolics rule out `I ≤ N_G(plane)`. This makes the actual rectangle
characteristic in I, without assuming that the ambient group is simple.

This supplies the characteristic-rectangle step of Aschbacher, *Sporadic
Groups* (1994), 41.3, printed p.222, for the marked comparison argument.
-/

public noncomputable section
open Subgroup
open BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
open SourceGeometry
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (hlinear : F.LinearFusion)

abbrev rowThreeIntersection : Subgroup G :=
  rowNormalizer F ⊓ sourceThreeSpaceNormalizer F

omit [Finite G] in
theorem threeSpace_le_rowThreeIntersection : F.threeSpace ≤ rowThreeIntersection F :=
  le_inf ((F.pullback_le _).trans (point_centralizer_le_row_normalizer F))
    F.threeSpace.le_normalizer

theorem sylow_le_rowThreeIntersection :
    (sourceSylow F : Subgroup G) ≤ rowThreeIntersection F :=
  le_inf ((sourceSylow_le_point_centralizer F).trans (point_centralizer_le_row_normalizer F))
    (plane_normalizers_contain_sourceSylow F).2

include hlinear

theorem rowThreeIntersection_not_le_plane :
    ¬ rowThreeIntersection F ≤ sourcePlaneNormalizer F := by
  intro h
  have hh : (sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F) ≤
      (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) :=
    fun x hx => h ⟨x.property, hx⟩
  rcases (plane_flag_maximal F hlinear).le_iff.mp hh with he | he
  · exact (line_flag_maximal F hlinear).ne_top he
  · exact line_plane_flag_ne F hlinear he

theorem normal_large_elementary_in_intersection
    (E : Subgroup (rowThreeIntersection F)) [E.Normal] [IsElementaryAbelian 2 E]
    (hcard : 64 ≤ Nat.card E) :
    E = F.threeSpace.subgroupOf (rowThreeIntersection F) := by
  let T := (sourceSylow F).subtype (sylow_le_rowThreeIntersection F)
  have hET : E ≤ (T : Subgroup (rowThreeIntersection F)) :=
    (IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal T
  let J := rowThreeIntersection F
  let A := E.map J.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map J.subtype
  have hAT : A ≤ (sourceSylow F : Subgroup G) := by
    rintro _ ⟨e, he, rfl⟩
    exact hET he
  have hc : 64 ≤ Nat.card A := by
    rwa [card_map_of_injective J.subtype_injective]
  rcases source_large_elementary_eq F A hAT hc with hA | hA
  · have hAJ : A ≤ J := map_subtype_le E
    have hE : A.subgroupOf J = E := comap_map_eq_self_of_injective J.subtype_injective E
    have hnorm : (A.subgroupOf J).Normal := by rw [hE]; infer_instance
    have hle := (normal_subgroupOf_iff_le_normalizer hAJ).mp hnorm
    rw [hA] at hle
    exact (rowThreeIntersection_not_le_plane F hlinear hle).elim
  · have he := congrArg (Subgroup.comap J.subtype) hA
    rw [comap_map_eq_self_of_injective J.subtype_injective] at he
    exact he

theorem intersection_threeSpace_characteristic :
    (F.threeSpace.subgroupOf (rowThreeIntersection F)).Characteristic := by
  let A := F.threeSpace.subgroupOf (rowThreeIntersection F)
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer
    (threeSpace_le_rowThreeIntersection F)).mpr inf_le_right
  let : IsElementaryAbelian 2 F.threeSpace := marked_rectangle_elementary F 3
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (threeSpace_le_rowThreeIntersection F)).toMonoidHom
    (subgroupOfEquivOfLe (threeSpace_le_rowThreeIntersection F)).injective
  apply characteristic_iff_map_eq.mpr
  intro a
  let : IsElementaryAbelian 2 (A.map a.toMonoidHom) := IsElementaryAbelian.map _
  let : (A.map a.toMonoidHom).Normal := (inferInstance : A.Normal).map _ a.surjective
  apply normal_large_elementary_in_intersection F hlinear
  rw [card_map_of_injective a.injective,
    Nat.card_congr (subgroupOfEquivOfLe (threeSpace_le_rowThreeIntersection F)).toEquiv,
    source_threeSpace_card]

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
