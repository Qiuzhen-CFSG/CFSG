module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.DesignProjection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.HexadCoverRestriction
public import Theory.Mathieu.M22.ValueBoundParabolics.CoverGeneration

/-!
# Cubic survival in the native hexad and generation across it

Apply the Chapter 13 cubic restriction argument to the actual component
projection. Transfer at index 77 retains the center in the derived group,
and the abelian two-kernel of the six-point action retains it in the
solvable residual. The residual supplies a perfect subgroup containing
and centralized by the cubic kernel, so every supplement is the whole
native hexad preimage.

Source: Aschbacher--Smith H.12.1(4), pp.393--394, and 14.4.12, pp.1011--1012.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover

noncomputable def innerPreimage (b : Finset (Fin 22)) : Subgroup M22TripleCover :=
  (MulAction.stabilizer M22 b).comap componentProjection

noncomputable def innerProjection (b : Finset (Fin 22)) :
    innerPreimage b →* MulAction.stabilizer M22 b :=
  componentProjection.subgroupComap _

theorem innerProjection_surjective (b : Finset (Fin 22)) :
    Function.Surjective (innerProjection b) :=
  componentProjection.subgroupComap_surjective_of_surjective _ componentProjection_surjective

theorem innerProjection_ker (b : Finset (Fin 22)) :
    (innerProjection b).ker = (center M22TripleCover).subgroupOf (innerPreimage b) := by
  ext x
  change innerProjection b x = 1 ↔ _
  rw [Subtype.ext_iff]
  change componentProjection x.val = 1 ↔ _
  rw [← MonoidHom.mem_ker, componentProjection_ker]
  rfl

theorem center_le_innerPreimage (b : Finset (Fin 22)) :
    center M22TripleCover ≤ innerPreimage b := by
  rw [← componentProjection_ker]
  exact ker_le_comap _ _

theorem innerProjection_kernel_central (b : Finset (Fin 22)) :
    (innerProjection b).ker ≤ center (innerPreimage b) := by
  rw [innerProjection_ker]
  intro x hx
  exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y.val)

theorem innerProjection_kernel_card (b : Finset (Fin 22)) :
    Nat.card (innerProjection b).ker = 3 := by
  rw [innerProjection_ker,
    Nat.card_congr (subgroupOfEquivOfLe (center_le_innerPreimage b)).toEquiv,
    M22TripleCover.center_card]

theorem innerPreimage_index {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (innerPreimage b).index = 77 := by
  rw [innerPreimage, index_comap_of_surjective _ componentProjection_surjective]
  have hc := (MulAction.stabilizer M22 b).card_mul_index
  rw [m22Hexad_stabilizer_card hb, m22_order] at hc
  omega

theorem innerProjection_kernel_le_derived {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (innerProjection b).ker ≤ commutator (innerPreimage b) := by
  have ht := central_le_mapped_commutator_of_coprime_index
    (innerPreimage b) (center M22TripleCover) le_rfl
    (center_le_innerPreimage b) (by
      rw [M22TripleCover.center_card, innerPreimage_index hb]; decide)
  rw [innerProjection_ker]
  intro x hx
  obtain ⟨y, hy, he⟩ := ht hx
  exact (Subtype.ext he : y = x) ▸ hy

/-- The literal component center survives in the native hexad residual. -/
theorem innerProjection_kernel_le_residual {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (innerProjection b).ker ≤ solvableResidual (innerPreimage b) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let r := CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.hexadNativeSixProjection hb
  have hr : Function.Surjective r :=
    (m22HexadQuotientAlternatingEquiv hb).surjective.comp (QuotientGroup.mk'_surjective _)
  have he : r.ker = (m22SetAction b).ker := CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.hexadNativeSixProjection_ker hb
  let : IsMulCommutative r.ker := by
    rw [he]
    let := m22HexadKernel_elementaryAbelian hb
    infer_instance
  have hp : IsPGroup 2 r.ker := by
    rw [he]
    exact IsPGroup.of_card (n := 4) (m22HexadKernel_card hb)
  exact CubicCentralRestriction.kernel_le_solvableResidual _
    (innerProjection_surjective b) (innerProjection_kernel_central b)
    (innerProjection_kernel_card b) (innerProjection_kernel_le_derived hb) r hr hp

noncomputable def innerNativeInclusion (b : Finset (Fin 22)) :
    innerPreimage b →* hexadPreimage b where
  toFun x := ⟨componentInclusion x.val, by
    change designProjection (componentInclusion x.val) ∈ MulAction.stabilizer m22DesignAut b
    rw [designProjection_component]
    exact x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def perfectSubgroup (b : Finset (Fin 22)) : Subgroup (hexadPreimage b) :=
  (solvableResidual (innerPreimage b)).map (innerNativeInclusion b)

instance perfectSubgroup_isPerfect (b : Finset (Fin 22)) : Group.IsPerfect (perfectSubgroup b) :=
  Group.IsPerfect.ofSurjective (f := (innerNativeInclusion b).subgroupMap _)
    ((innerNativeInclusion b).subgroupMap_surjective _)

theorem kernel_le_perfectSubgroup {b : Finset (Fin 22)} (hb : b ∈ m22Blocks) :
    (localProjection (MulAction.stabilizer m22DesignAut b)).ker ≤ perfectSubgroup b := by
  intro x hx
  rw [localProjection_ker] at hx
  change x.val ∈ cubic at hx
  rw [cubic_eq_map_center] at hx
  obtain ⟨z, hz, he⟩ := hx
  let y : innerPreimage b := ⟨z, center_le_innerPreimage b hz⟩
  have hy : y ∈ (innerProjection b).ker := by
    rw [innerProjection_ker]
    exact hz
  exact ⟨y, innerProjection_kernel_le_residual hb hy, Subtype.ext he⟩

theorem kernel_centralizes_perfectSubgroup (b : Finset (Fin 22)) :
    (localProjection (MulAction.stabilizer m22DesignAut b)).ker ≤
      centralizer (perfectSubgroup b : Set (hexadPreimage b)) := by
  intro x hx y hy
  obtain ⟨z, _, rfl⟩ := hy
  rw [localProjection_ker] at hx
  exact Subtype.ext (cubic_le_centralizer_component hx _ z.val.property)

/-- A subgroup covering the actual design hexad stabilizer is its full native preimage. -/
theorem eq_hexadPreimage_of_map {b : Finset (Fin 22)} (hb : b ∈ m22Blocks)
    (J : Subgroup Model) (hJ : J ≤ hexadPreimage b)
    (hmap : J.map designProjection = MulAction.stabilizer m22DesignAut b) :
    J = hexadPreimage b := by
  let f : hexadPreimage b →* MulAction.stabilizer m22DesignAut b :=
    localProjection (MulAction.stabilizer m22DesignAut b)
  have hm : (J.subgroupOf (hexadPreimage b)).map f = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨x, hx, he⟩ := (show y.val ∈ J.map designProjection from hmap.symm ▸ y.property)
    exact ⟨⟨x, hJ hx⟩, hx, Subtype.ext he⟩
  have hg : f.ker ⊔ J.subgroupOf (hexadPreimage b) = ⊤ := by
    have he := congrArg (comap f) hm
    simpa only [comap_map_eq, comap_top, sup_comm] using he
  have ht := M22ValueBound.eq_top_of_central_perfect_supplement
    (perfectSubgroup b) f.ker (J.subgroupOf (hexadPreimage b))
    (kernel_le_perfectSubgroup hb) (kernel_centralizes_perfectSubgroup b) hg
  exact hJ.antisymm (subgroupOf_eq_top.mp ht)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.HexadCover
