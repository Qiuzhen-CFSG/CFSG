module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonCompletion

/-!
# A forced central eight in the common-image case

Each nonidentity common-image actor has the same eight fixed kernel masks
under its centralizer in the actual 96-element pair image. Consequently all
eight elements lie in the full ambient double centralizer of every pure
extension with nontrivial common image, for every actual lift and kernel.

The full-image consumer combines this lower bound with the pure
128-element completion and the equality of whole normalizers at maximal
TWO-local level. Mask 1257 is a proved central involution here, but its
intrinsic uniqueness and final whole-normalizer placement are not assumed.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis
set_option backward.isDefEq.respectTransparency true

/-- The eight kernel elements forced into the center of every actual
centralizer with nontrivial common image. -/
@[expose] def commonCenterMask : Fin 8 → ℕ := ![0,320,626,818,1257,1449,1691,2011]

private theorem center_fixed : ∀ (i : Fin 96) (j : Fin 3) (k : Fin 8),
    (element i).val * (element (pureIndex 1 j)).val =
      (element (pureIndex 1 j)).val * (element i).val →
    SylowCore.starMask (element i) (commonCenterMask k) = commonCenterMask k := by decide +kernel

/-- This is membership in the full ambient double centralizer, independent
of every choice of lift and of the size of the actual kernel. -/
theorem common_center_kernel_mem (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) (k : Fin 8) :
    (kernelValue (commonCenterMask k) : Model) ∈
      centralizer (centralizer (X : Set Model) : Set Model) := by
  obtain ⟨p,hp⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hp1 : p.val ≠ 1 := fun he => hp (Subtype.ext he)
  obtain ⟨j,hj⟩ := pure_position_image_coordinates X hpair hpure 1 hpos p.val p.property hp1
  obtain ⟨w,hw,hwq⟩ := p.property
  intro z hz
  have hzM := (elementary_overgroup_placement X hpair).2 hz
  let u : M := ⟨z,hzM⟩
  have hu : u ∈ localPairCentralizer := by
    have hP := (centralizer_le hpair) hz
    rintro v (rfl | rfl)
    · exact Subtype.ext (hP _ (subset_closure (by simp)))
    · exact Subtype.ext (hP _ (subset_closure (by simp)))
  obtain ⟨i,hi⟩ := (mem_pair_image_iff (starHom u)).mp (mem_map_of_mem starHom hu)
  have hcomm : (element i).val * (element (pureIndex 1 j)).val =
      (element (pureIndex 1 j)).val * (element i).val := by
    have he : w * u = u * w := Subtype.ext (hz _ hw)
    have heq := congrArg (fun v : StarGroup => v.val) (congrArg starHom he.symm)
    simpa only [map_mul,hi,hwq,hj,Subgroup.coe_mul] using heq
  have hc := kernel_conjugation u (commonCenterMask k)
  change u * kernelValue (commonCenterMask k) * u⁻¹ =
    kernelValue (SylowCore.starMask (starHom u) (commonCenterMask k)) at hc
  rw [← hi,center_fixed i j k hcomm] at hc
  exact congrArg (fun v : M => (v : Model)) (mul_inv_eq_iff_eq_mul.mp hc)

/-- In particular the candidate source central involution lies in the
intrinsic double centralizer; its uniqueness still requires rank geometry. -/
theorem common_center_involution_mem (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    (kernelValue 1257 : Model) ∈ centralizer (centralizer (X : Set Model) : Set Model) ∧
      orderOf (kernelValue 1257 : Model) = 2 := by
  refine ⟨common_center_kernel_mem X hpair hpure hpos hne 4,?_⟩
  have hp : IsConj a (kernelValue 1257 : Model) := by
    apply commonSpace_pure
    · exact (mem_commonSpace _).mpr ⟨16,rfl⟩
    · intro h
      have h' : kernelValue 1257 = kernelValue 0 := (Subtype.ext h).trans kernelValue_zero.symm
      have he := kernelValue_injective (by decide : 1257 < 2048) (by decide : 0 < 2048) h'
      contradiction
  obtain ⟨g,hg⟩ := isConj_iff.mp hp
  rw [← hg]
  exact ((MulAut.conj g).orderOf_eq a).trans orderOf_a

/-- Actual common-position maximal extensions admit an intrinsic pure
replacement with the same WHOLE normalizer and the specified central
involution. No selected lift is assumed normalized. -/
theorem common_four_intrinsic_replacement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    let Z := centralizer (centralizer (X : Set Model) : Set Model)
    X ≤ Z ∧ IsElementaryAbelian 2 Z ∧
      (∀ z ∈ Z, z ≠ 1 → IsConj a z) ∧
      Z ≤ commonCompletion X ∧ Nat.card (commonCompletion X) = 128 ∧
      (kernelValue 1257 : Model) ∈ Z ∧
      normalizer (Z : Set Model) = normalizer (X : Set Model) := by
  have he := pure_position_image_eq X hpair hpure 1 hpos hfour
  obtain ⟨hXZ,hZ,hpureZ,hNZ⟩ := common_double_centralizer_maximal X hpair hpure he hmax
  have hn := maximal_pure_extension_image_ne_bot X hpair hpure hmax
  exact ⟨hXZ,hZ,hpureZ,(common_double_centralizer_bounds X hpair he).2,
    commonCompletion_card X hpair he,(common_center_involution_mem X hpair hpure hpos hn).1,hNZ⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
