module
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Mathlib.FieldTheory.Finiteness
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Incidence
public import Theory.Mathieu.M24.ChapterHStabilizers.CommonPlane
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Orders

/-!
# The literal native point–plane parabolic

The marked octad is the union of two specified hexacode columns. Its
stabilizer in the sextet group is the preimage of the corresponding pair
stabilizer in S₆ and has order 9216. The intersection of the intrinsic
sextet and octad cores is a four-group; its octad coordinates give a
binary two-space. Normality of both cores places the point–plane group
in its parabolic, and the independently computed orders give equality.

This identifies the actual native intersection needed in Aschbacher,
*Sporadic Groups* (1994), 41.4, p.222, using the native geometry of
19.8–19.9, pp.96–97. The source comparison uses this identity in
`AlignPlane`; no abstract isomorphism type replaces a marked subgroup.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativePlane
open Sporadic.Mathieu.M24ChapterHStabilizers
open OctadAction MathieuCode

/-- The vertex in the uniqueness system is the original marked native octad. -/
theorem first_eq_standardOctad : first = standardOctad := by
  apply Subtype.ext
  decide +kernel

/-- The literal octad condition is the stabilizer of its pair of hexacode columns. -/
theorem sextet_mem_octad_iff (g : sextetStabilizer standardSextet) :
    (g : M24) ∈ octadStabilizer standardOctad ↔
      SextetCore.columnHom g ∈
        MulAction.stabilizer (Equiv.Perm (Fin 6)) CommonPlane.basePair.val := by
  rw [octadStabilizer, MulAction.mem_stabilizer_finset, MulAction.mem_stabilizer_finset]
  constructor
  · intro h j
    let i := Atlas.Codes.hexPos j
    have hh := h (atlasPointEquiv (i, 0))
    obtain ⟨⟨a,b⟩, hab⟩ := atlasPointEquiv.surjective ((g : M24) • atlasPointEquiv (i, 0))
    rw [← hab, CommonPlane.octad_coordinates, CommonPlane.octad_coordinates] at hh
    have hc := SextetCore.columnHom_apply g i 0
    change SextetCore.columnHom g (Atlas.Codes.hexIndexEquiv i) = _ at hc
    change atlasPointEquiv (a,b) = g.val.val _ at hab
    rw [← hab, atlasPointEquiv.symm_apply_apply] at hc
    change SextetCore.columnHom g j ∈ CommonPlane.basePair.val ↔ j ∈ CommonPlane.basePair.val
    simpa only [i, ← hc, Atlas.Codes.index_hexPos] using hh
  · intro h x
    obtain ⟨⟨i,k⟩, rfl⟩ := atlasPointEquiv.surjective x
    obtain ⟨⟨a,b⟩, hab⟩ := atlasPointEquiv.surjective ((g : M24) • atlasPointEquiv (i,k))
    rw [← hab, CommonPlane.octad_coordinates, CommonPlane.octad_coordinates]
    have hc := SextetCore.columnHom_apply g i k
    change atlasPointEquiv (a,b) = g.val.val _ at hab
    rw [← hab, atlasPointEquiv.symm_apply_apply] at hc
    rw [← hc]
    exact h _

/-- The native point–plane stabilizer has order 9216. -/
theorem point_plane_card :
    Nat.card ↥(octadStabilizer standardOctad ⊓ sextetStabilizer standardSextet) = 9216 := by
  let J := MulAction.stabilizer (Equiv.Perm (Fin 6)) CommonPlane.basePair.val
  have hJ : Nat.card J = 48 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hi : J.index = 15 := by
    have h := J.card_mul_index
    rw [hJ, Nat.card_perm] at h
    norm_num [Nat.factorial] at h
    omega
  have he : (octadStabilizer standardOctad).subgroupOf (sextetStabilizer standardSextet) =
      J.comap SextetCore.columnHom := by
    ext g
    exact sextet_mem_octad_iff g
  have h := ((octadStabilizer standardOctad).subgroupOf
    (sextetStabilizer standardSextet)).card_mul_index
  rw [he, index_comap_of_surjective _ SextetCore.columnHom_surjective,
    hi, SextetCore.stabilizer_card] at h
  have hc := card_map_of_injective
    (K := (octadStabilizer standardOctad).subgroupOf (sextetStabilizer standardSextet))
    (sextetStabilizer standardSextet).subtype_injective
  rw [subgroupOf_map_subtype, he] at hc
  omega

/-- Coordinates of the common four inside the intrinsic octad kernel. -/
@[expose] def commonSubspace : Submodule (ZMod 2) Space where
  carrier := {v | ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) :
    M24) ∈ SextetCore.core}
  zero_mem' := by
    change ((ambientCoordinates standardOctad).symm 1 : M24) ∈ SextetCore.core
    simp
  add_mem' := by
    intro v w hv hw
    change ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v *
      Multiplicative.ofAdd w) : M24) ∈ SextetCore.core
    simpa only [map_mul, Subgroup.coe_mul] using SextetCore.core.mul_mem hv hw
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa only [one_smul] using hv

@[simp] theorem coordinates_mem_commonSubspace (a : AmbientCore standardOctad) :
    (ambientCoordinates standardOctad a).toAdd ∈ commonSubspace ↔
      (a : M24) ∈ SextetCore.core := by
  change ((ambientCoordinates standardOctad).symm (ambientCoordinates standardOctad a) :
    M24) ∈ SextetCore.core ↔ _
  rw [MulEquiv.symm_apply_apply]

private def commonEquiv : commonSubspace ≃ CommonPlane.common where
  toFun v := ⟨(ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v.val),
    ((ambientCoordinates standardOctad).symm _).property, v.property⟩
  invFun a := ⟨(ambientCoordinates standardOctad ⟨a, a.property.1⟩).toAdd,
    (coordinates_mem_commonSubspace _).mpr a.property.2⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd
      ((ambientCoordinates standardOctad).apply_symm_apply (Multiplicative.ofAdd v.val))
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun x : AmbientCore standardOctad => (x : M24))
      ((ambientCoordinates standardOctad).symm_apply_apply ⟨a, a.property.1⟩)

/-- The common four is a two-space in the natural row module. -/
theorem commonSubspace_finrank : Module.finrank (ZMod 2) commonSubspace = 2 := by
  have hc := (Nat.card_congr commonEquiv).trans CommonPlane.common_card
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc.trans (by decide : 4 = 2 ^ 2))

private theorem stabilizer_normalizes_core (H : Subgroup M24) :
    H ≤ normalizer (((pCore 2 H).map H.subtype : Subgroup M24) : Set M24) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨g, hg⟩ * y * (⟨g, hg⟩ : H)⁻¹,
    (inferInstance : (pCore 2 H).Normal).conj_mem y hy ⟨g, hg⟩, rfl⟩

/-- The actual point–plane intersection preserves its common kernel two-space. -/
theorem point_plane_le_parabolic :
    (sextetStabilizer standardSextet).subgroupOf (Stabilizer standardOctad) ≤
      (BinaryLinear.parabolic commonSubspace).comap (linearAction standardOctad) := by
  intro g hg v
  have hn := stabilizer_normalizes_core (sextetStabilizer standardSextet) hg
  have ha := ambientCoordinates_conjugation standardOctad g v
  rw [naturalAction_quotientEquiv] at ha
  change ((ambientCoordinates standardOctad).symm
    (Multiplicative.ofAdd (linearAction standardOctad g v)) : M24) ∈ SextetCore.core ↔
      ((ambientCoordinates standardOctad).symm (Multiplicative.ofAdd v) : M24) ∈ SextetCore.core
  rw [← ha]
  exact (mem_normalizer_iff.mp hn _).symm

/-- The common two-space gives exactly the native point–plane stabilizer,
under the literal octad quotient action. -/
theorem plane_parabolic_comap :
    (BinaryLinear.parabolic commonSubspace).comap (linearAction standardOctad) =
      (sextetStabilizer standardSextet).subgroupOf (Stabilizer standardOctad) := by
  apply (eq_of_le_of_card_ge point_plane_le_parabolic _).symm
  have hi : ((BinaryLinear.parabolic commonSubspace).comap
      (linearAction standardOctad)).index = 35 := by
    rw [index_comap_of_surjective _ (linearAction_surjective standardOctad)]
    exact BinaryLinear.FourParabolicAction.twoSpace_parabolic_index _ (by simp)
      commonSubspace_finrank
  have h := ((BinaryLinear.parabolic commonSubspace).comap
    (linearAction standardOctad)).card_mul_index
  rw [hi, octadStabilizer_card] at h
  have hc := card_map_of_injective
    (K := (sextetStabilizer standardSextet).subgroupOf (Stabilizer standardOctad))
    (Stabilizer standardOctad).subtype_injective
  rw [subgroupOf_map_subtype, inf_comm, point_plane_card] at hc
  omega

end Sporadic.Mathieu.M24LocalGeometry.OctadGraph.NativePlane
