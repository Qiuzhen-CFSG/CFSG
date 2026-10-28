module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.LinePlane
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders
public import Theory.SpecificGroups.SymmetricSix.CubicExtensionMaximality

/-!
# Source plane orders and local generation

The point–plane stabilizer has order 16·576 = 9216, computed through the
literal row action. The plane stabilizer has order 64·3·720 = 138240.
Its fifteen point cosets therefore have a maximal stabilizer: first pass
through A₂ and then use the cubic-extension maximality theorem. The marked
edge reversal leaves this stabilizer, proving both plane flag generation
and the local-generation identity in the source uniqueness system.

Only the original `SourceNormalizer.LocalData` is assumed. Global generation
and the compatible source-to-native local isomorphisms remain separate
obligations; no recognition premise is used in these local calculations.

Source: Aschbacher, *Sporadic Groups* (1994), 41.1 and 41.4, pp.219–222.
-/

public noncomputable section
open Subgroup Module
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z) (D : LocalData F)
include D

omit [Finite G] in
/-- The full row normalizer has order 322560. -/
theorem row_normalizer_card : Nat.card (rowNormalizer F) = 322560 := by
  rw [card_eq_card_quotient_mul_card_subgroup (F.row.subgroupOf (rowNormalizer F)),
    Nat.card_congr (D.rowEquiv F).toEquiv,
    BinaryFourFixedSpace.card_GL_four (by simp),
    Nat.card_congr (subgroupOfEquivOfLe F.row.le_normalizer).toEquiv, row_card F]

omit [Finite G] in
/-- There are 35 marked planes through a source point. -/
theorem point_plane_index : (threeSpaceNormalizer F).relIndex (rowNormalizer F) = 35 := by
  change ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F)).index = _
  rw [← plane_parabolic_comap F D,
    index_comap_of_surjective _ (rowAction_surjective F D)]
  exact BinaryLinear.FourParabolicAction.twoSpace_parabolic_index _ (by simp)
    (row_threeSpace_finrank F)

omit [Finite G] in
/-- The literal point–plane intersection has order 9216. -/
theorem point_plane_card : Nat.card ↥(rowNormalizer F ⊓ threeSpaceNormalizer F) = 9216 := by
  have h := ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F)).card_mul_index
  change Nat.card ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F)) *
    (threeSpaceNormalizer F).relIndex (rowNormalizer F) = _ at h
  rw [point_plane_index F D, row_normalizer_card F D] at h
  have hc := card_map_of_injective (K := (threeSpaceNormalizer F).subgroupOf (rowNormalizer F))
    (f := (rowNormalizer F).subtype) (rowNormalizer F).subtype_injective
  rw [subgroupOf_map_subtype, inf_comm] at hc
  omega

omit [Finite G] in
/-- The plane quotient has order 2160 from its cubic kernel and S₆ quotient. -/
theorem threeSpace_quotient_card : Nat.card (threeSpaceQuotient F) = 2160 := by
  let := D.cubicKernel_normal
  rw [card_eq_card_quotient_mul_card_subgroup D.cubicKernel,
    Nat.card_congr D.cubicKernel_quotient.some.toEquiv, D.cubicKernel_card]
  norm_num [Nat.card_perm, Fintype.card_perm, Nat.factorial]

omit [Finite G] in
/-- The full plane normalizer has order 138240. -/
theorem threeSpace_normalizer_card : Nat.card (threeSpaceNormalizer F) = 138240 := by
  rw [card_eq_card_quotient_mul_card_subgroup (F.threeSpace.subgroupOf (threeSpaceNormalizer F)),
    threeSpace_quotient_card F D,
    Nat.card_congr (subgroupOfEquivOfLe F.threeSpace.le_normalizer).toEquiv,
    threeSpace_card F]

omit [Finite G] in
/-- The literal point stabilizer has index 15 in the plane normalizer. -/
theorem plane_point_index : (rowNormalizer F).relIndex (threeSpaceNormalizer F) = 15 := by
  have h := ((rowNormalizer F).subgroupOf (threeSpaceNormalizer F)).card_mul_index
  have hc := card_map_of_injective (K := (rowNormalizer F).subgroupOf (threeSpaceNormalizer F))
    (f := (threeSpaceNormalizer F).subtype) (threeSpaceNormalizer F).subtype_injective
  rw [subgroupOf_map_subtype, point_plane_card F D] at hc
  rw [← hc, threeSpace_normalizer_card F D] at h
  change _ * (rowNormalizer F).relIndex (threeSpaceNormalizer F) = _ at h
  omega

omit D [Finite G] in
/-- The marked rectangle lies in the full row normalizer. -/
theorem threeSpace_le_row_normalizer : F.threeSpace ≤ rowNormalizer F :=
  (F.pullback_le _).trans (point_centralizer_le_row_normalizer F)

/-- The point stabilizer in a plane is maximal in the literal ambient plane normalizer. -/
theorem plane_point_maximal :
    IsCoatom ((rowNormalizer F).subgroupOf (threeSpaceNormalizer F)) := by
  let A := F.threeSpace.subgroupOf (threeSpaceNormalizer F)
  let J := (rowNormalizer F).subgroupOf (threeSpaceNormalizer F)
  let q := QuotientGroup.mk' A
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective A
  have hk : q.ker ≤ J := by
    rw [QuotientGroup.ker_mk']
    exact fun a ha => threeSpace_le_row_normalizer F ha
  have hi : (J.map q).index = 15 := by
    rw [index_map_eq _ hq hk]
    exact plane_point_index F D
  let := D.cubicKernel_normal
  have hm := SymmetricSix.CubicExtension.index_fifteen_maximal_of_cubic
    D.cubicKernel (J.map q) D.cubicKernel_card D.cubicKernel_quotient.some hi
  have he : (J.map q).comap q = J := by
    rw [comap_map_eq, sup_eq_left.mpr hk]
  change IsCoatom J
  rw [← he]
  exact isCoatom_comap_of_surjective hq hm

open GraphUniquenessSystem GraphUniquenessSystem.Cosets

omit [Finite G] in
/-- Each source plane has exactly fifteen literal point cosets. -/
theorem plane_point_card : Nat.card (Residue (threeSpaceNormalizer F) (rowNormalizer F)) = 15 := by
  rw [← Nat.card_congr (residueEquiv (threeSpaceNormalizer F) (rowNormalizer F))]
  exact plane_point_index F D

/-- The two actual flag stabilizers generate the plane stabilizer. -/
theorem plane_flag_generate :
    (rowNormalizer F ⊓ threeSpaceNormalizer F) ⊔
      (planeNormalizer F ⊓ threeSpaceNormalizer F) = threeSpaceNormalizer F := by
  let K := (rowNormalizer F ⊓ threeSpaceNormalizer F) ⊔
    (planeNormalizer F ⊓ threeSpaceNormalizer F)
  have hle : K ≤ threeSpaceNormalizer F := sup_le inf_le_right inf_le_right
  have hj : (rowNormalizer F).subgroupOf (threeSpaceNormalizer F) ≤
      K.subgroupOf (threeSpaceNormalizer F) := fun a ha => mem_sup_left ⟨ha, a.property⟩
  have htop : K.subgroupOf (threeSpaceNormalizer F) = ⊤ := by
    apply (plane_point_maximal F D).2
    refine lt_of_le_of_ne hj ?_
    intro he
    have hmem : (⟨(planeSwap F D : G), planeSwap_mem F D⟩ : threeSpaceNormalizer F) ∈
        K.subgroupOf (threeSpaceNormalizer F) :=
      mem_sup_right ⟨(planeSwap F D).property, planeSwap_mem F D⟩
    rw [← he] at hmem
    exact planeSwap_not_row F D hmem
  apply le_antisymm hle
  intro a ha
  exact show (⟨a, ha⟩ : threeSpaceNormalizer F) ∈ K.subgroupOf (threeSpaceNormalizer F) from
    htop ▸ mem_top _

/-- The local-generation identity uses the actual point and unordered-edge stabilizers. -/
theorem local_generate :
    (threeSpaceNormalizer F ⊓ edgeStabilizer G (vertex (rowNormalizer F) 1)
      (vertex (rowNormalizer F) (planeSwap F D : G))) ⊔
        (threeSpaceNormalizer F ⊓ MulAction.stabilizer G (vertex (rowNormalizer F) 1)) =
      threeSpaceNormalizer F := by
  rw [stabilizer_base]
  let K := (threeSpaceNormalizer F ⊓ edgeStabilizer G (vertex (rowNormalizer F) 1)
    (vertex (rowNormalizer F) (planeSwap F D : G))) ⊔
      (threeSpaceNormalizer F ⊓ rowNormalizer F)
  have hle : K ≤ threeSpaceNormalizer F := sup_le inf_le_left inf_le_left
  have hj : (rowNormalizer F).subgroupOf (threeSpaceNormalizer F) ≤
      K.subgroupOf (threeSpaceNormalizer F) := fun a ha => mem_sup_right ⟨a.property, ha⟩
  have htop : K.subgroupOf (threeSpaceNormalizer F) = ⊤ := by
    apply (plane_point_maximal F D).2
    refine lt_of_le_of_ne hj ?_
    intro he
    have hedge : (planeSwap F D : G) ∈ edgeStabilizer G (vertex (rowNormalizer F) 1)
        (vertex (rowNormalizer F) (planeSwap F D : G)) := by
      refine Or.inr ⟨by simp, ?_⟩
      rw [smul_vertex]
      exact (vertex_eq_base _ _).mpr (planeSwap_square_mem F D)
    have hmem : (⟨(planeSwap F D : G), planeSwap_mem F D⟩ : threeSpaceNormalizer F) ∈
        K.subgroupOf (threeSpaceNormalizer F) := mem_sup_left ⟨planeSwap_mem F D, hedge⟩
    rw [← he] at hmem
    exact planeSwap_not_row F D hmem
  apply le_antisymm hle
  intro a ha
  exact show (⟨a, ha⟩ : threeSpaceNormalizer F) ∈ K.subgroupOf (threeSpaceNormalizer F) from
    htop ▸ mem_top _

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
