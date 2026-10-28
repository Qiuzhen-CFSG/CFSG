module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.PlaneKernelComparison
public import Theory.Mathieu.M24.ChapterHStabilizers.CommonPlane

/-!
# The source common four in native hexacode geometry

The original row–three-space intersection gives a binary two-space in the
constructed plane coordinates. Its point–plane group preserves it. The
normal cubic lies in this group because it is the plane-point action kernel;
under the proved full quotient comparison it supplies the F4 scalar operator.
The common four is therefore an F4 line. It contains the distinguished source
involution, whose coordinate has weight four, excluding the full-weight lines.
The native field-line classification identifies it as a double-zero plane.

Consequently the actual plane isomorphism sends the literal source intersection
to the native subgroup associated with a pair of hexacode columns. This provides
the geometric input for aligning the point–plane flag, without assuming that
abstract four-groups or abstract plane groups have compatible embeddings.

Source: Aschbacher, *Sporadic Groups* (1994), 41.4, p.222; the native
common-four geometry is 19.9, pp.96–97, also Aschbacher–Smith H.14.1(6), p.397.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
open Atlas.Codes Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.Hexacode
open BinaryPermutation.SixPairsQuadratic (Pair)
variable {G : Type*} [Group G] [Finite G] {z : G}
  (F : MarkedCentralizer z) (D : LocalData F)

/-- The actual row–plane common four in the original hexacode coordinates. -/
@[expose] def planeCommonSubspace : Submodule Bit hexacode where
  carrier := {v | ((threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd v) : G) ∈ F.row}
  zero_mem' := by
    change ((threeSpaceHexCoordinates F).symm 1 : G) ∈ F.row
    simp
  add_mem' := by
    intro v w hv hw
    change ((threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : G) ∈ F.row
    simpa only [map_mul,Subgroup.coe_mul] using F.row.mul_mem hv hw
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : Bit, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa only [one_smul] using hv

private def commonEquiv : planeCommonSubspace F ≃ ↥(F.row ⊓ F.threeSpace) where
  toFun v := ⟨(threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd v.val),
    v.property,((threeSpaceHexCoordinates F).symm _).property⟩
  invFun a := ⟨(threeSpaceHexCoordinates F ⟨a,a.property.2⟩).toAdd,by
    change ((threeSpaceHexCoordinates F).symm (threeSpaceHexCoordinates F ⟨a,a.property.2⟩) : G) ∈ F.row
    rw [MulEquiv.symm_apply_apply]
    exact a.property.1⟩
  left_inv v := by
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd ((threeSpaceHexCoordinates F).apply_symm_apply _)
  right_inv a := by
    apply Subtype.ext
    exact congrArg (fun b : F.threeSpace => (b : G)) ((threeSpaceHexCoordinates F).symm_apply_apply _)

omit [Finite G] in
/-- The common four is a binary two-space in the native plane coordinates. -/
theorem planeCommonSubspace_finrank : Module.finrank Bit (planeCommonSubspace F) = 2 := by
  have hc := (Nat.card_congr (commonEquiv F)).trans (SourceNormalizer.row_threeSpace_card F)
  rw [Module.natCard_eq_pow_finrank (K := Bit),Nat.card_zmod] at hc
  exact Nat.pow_right_injective (by decide : 1 < 2) (hc.trans (by decide : 4 = 2^2))

/-- Every actual point–plane element preserves this common four under its literal quotient action. -/
theorem planeCommonSubspace_stable (n : threeSpaceNormalizer F)
    (hn : (n : G) ∈ rowNormalizer F) (v : hexacode) :
    hexAction (threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) v ∈ planeCommonSubspace F ↔
      v ∈ planeCommonSubspace F := by
  let a := (threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd v)
  have h := threeSpaceHexQuotientEquiv_action F D n a
  have ha : threeSpaceHexCoordinates F a = Multiplicative.ofAdd v :=
    (threeSpaceHexCoordinates F).apply_symm_apply _
  rw [ha] at h
  have hh := congrArg (threeSpaceHexCoordinates F).symm h
  rw [MulEquiv.symm_apply_apply] at hh
  change ((threeSpaceHexCoordinates F).symm
    (Multiplicative.ofAdd (hexAction (threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) v)) : G) ∈ F.row ↔ _
  change F.threeSpace.normalizerMonoidHom n a =
    (threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd
      (hexAction (threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) v)) at hh
  rw [← hh]
  exact (mem_normalizer_iff.mp hn (a : G)).symm

include D in
/-- The normal cubic already lies in the point–plane group; its actual scalar
operator makes the common four an F4 line. -/
theorem planeCommonSubspace_scalar_stable :
    hexZ ∈ Representation.BinaryOffender.subspaceStabilizer action (planeCommonSubspace F) := by
  have hm : hexZ ∈ D.cubicKernel.map (threeSpaceHexQuotientEquiv F D).toMonoidHom := by
    rw [threeSpaceHexQuotientEquiv_cubic,hexCoordinateSix_kernel]
    exact mem_zpowers hexZ
  obtain ⟨q,hq,hz⟩ := hm
  obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective
    (F.threeSpace.subgroupOf (threeSpaceNormalizer F)) q
  have hn : (n : G) ∈ rowNormalizer F := by
    apply ((rowNormalizer F).subgroupOf (threeSpaceNormalizer F)).normalCore_le
    rw [plane_point_core F D]
    exact hq
  intro v
  change hexAction hexZ v ∈ planeCommonSubspace F ↔ _
  rw [← hz]
  exact planeCommonSubspace_stable F D n hn v

omit [Finite G] in
/-- The image of the original marked point lies in the common four. -/
theorem planeCommonSubspace_point : PlaneComparison.hexCoordinates 4 ∈ planeCommonSubspace F := by
  change ((threeSpaceHexCoordinates F).symm (Multiplicative.ofAdd (PlaneComparison.hexCoordinates 4)) : G) ∈ F.row
  rw [← threeSpaceHexCoordinates_point F,MulEquiv.symm_apply_apply]
  exact point_mem_row F

include D in
/-- The common four is a literal double-zero plane of the native hexacode,
not merely an abstract elementary group of order four. -/
theorem planeCommonSubspace_is_pair : ∃ s : Pair, planeCommonSubspace F = zeroPairPlane s := by
  let L := scalarSubmodule (planeCommonSubspace F) (planeCommonSubspace_scalar_stable F D)
  have hd : Module.finrank Representation.Hexacode.F L = 1 := by
    have h := scalarSubmodule_finrank (planeCommonSubspace F) (planeCommonSubspace_scalar_stable F D)
    rw [planeCommonSubspace_finrank] at h
    change 2 * Module.finrank Representation.Hexacode.F L = 2 at h
    omega
  have hzero : PlaneComparison.hexCoordinates 4 ≠ 0 := by
    intro he
    have hp := threeSpaceHexCoordinates_point F
    rw [he] at hp
    have hh : (⟨z,point_mem_threeSpace F⟩ : F.threeSpace) = 1 :=
      (threeSpaceHexCoordinates F).map_eq_one_iff.mp hp
    have hz : z = 1 := congrArg Subtype.val hh
    have ho := F.point_orderOf
    rw [hz,orderOf_one] at ho
    omega
  have hwt : hammingNorm (PlaneComparison.hexCoordinates 4).val ≠ 6 := by
    intro h
    have he := (PlaneComparison.exceptional_iff_weight_six 4).mpr h
    exact (by decide : Sextet.exceptional 4 ≠ true) he
  rcases fieldPoint_full_or_pair L hd with hfull | ⟨s,hs⟩
  · exact False.elim (hwt (hfull.2.2
      ⟨PlaneComparison.hexCoordinates 4,planeCommonSubspace_point F⟩
      (fun he => hzero (congrArg Subtype.val he))))
  · exact ⟨s,hs⟩

include D in
/-- Under every comparison retaining the prescribed kernel, the actual common four
is the double-zero subgroup of a specific native column pair. -/
theorem native_plane_equiv_common_four
    (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet)
    (he : ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
      (M24ChapterHStabilizers.SextetAction.translationEquiv
        (threeSpaceHexCoordinates F a) : sextetStabilizer standardSextet)) :
    ∃ s : Pair,
      ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) =
          M24ChapterHStabilizers.CommonPlane.planeGroup s := by
  obtain ⟨s,hs⟩ := planeCommonSubspace_is_pair F D
  refine ⟨s,le_antisymm ?_ ?_⟩
  · rintro _ ⟨n,hn,rfl⟩
    let a : F.threeSpace := ⟨n,hn.2⟩
    have en : n = inclusion F.threeSpace.le_normalizer a := rfl
    change (e n : M24) ∈ _
    rw [en,he]
    apply (M24ChapterHStabilizers.CommonPlane.translation_mem_planeGroup s
      (threeSpaceHexCoordinates F a).toAdd).mpr
    rw [← hs]
    change ((threeSpaceHexCoordinates F).symm (threeSpaceHexCoordinates F a) : G) ∈ F.row
    rw [MulEquiv.symm_apply_apply]
    exact hn.1
  · rintro _ ⟨v,hv,rfl⟩
    let a := (threeSpaceHexCoordinates F).symm v
    have ha : (a : G) ∈ F.row := by
      change v.toAdd ∈ zeroPairPlane s at hv
      rw [← hs] at hv
      exact hv
    refine ⟨inclusion F.threeSpace.le_normalizer a,⟨ha,a.property⟩,?_⟩
    change (e (inclusion F.threeSpace.le_normalizer a) : M24) = _
    rw [he]
    have hh : threeSpaceHexCoordinates F a = v := (threeSpaceHexCoordinates F).apply_symm_apply _
    rw [hh]
    rfl

/-- The same concrete source plane map identifies its quotient action, full
plane-action kernel, and actual common four. -/
theorem exists_native_plane_equiv_common_four :
    ∃ (e : threeSpaceNormalizer F ≃* sextetStabilizer standardSextet) (s : Pair),
      (∀ n, SextetCore.quotientHom (e n) = threeSpaceHexQuotientEquiv F D (QuotientGroup.mk n)) ∧
      (planePointAction F).ker.map e.toMonoidHom = SextetCore.columnHom.ker ∧
      ((F.row ⊓ F.threeSpace).subgroupOf (threeSpaceNormalizer F)).map
        ((sextetStabilizer standardSextet).subtype.comp e.toMonoidHom) =
          M24ChapterHStabilizers.CommonPlane.planeGroup s := by
  obtain ⟨e,hker,hq,hk⟩ := exists_native_plane_equiv_action_kernel F D
  obtain ⟨s,hs⟩ := native_plane_equiv_common_four F D e hker
  exact ⟨e,s,hq,hk,hs⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
