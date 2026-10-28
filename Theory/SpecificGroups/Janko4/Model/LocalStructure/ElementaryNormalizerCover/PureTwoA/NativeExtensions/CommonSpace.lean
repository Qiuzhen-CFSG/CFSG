module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.KernelGeometry

/-!
# The common displacement space and its exact centralizers

The common Mathieu four-image has an explicit 32-element displacement
space in the original binary kernel. Its common fixed kernel is exactly
that space, and its pointwise stabilizer in the native pair image is the
same four-group. All nonidentity elements of the space are first-class.
Every one is a displacement of each nonidentity common-image actor.

These exhaustive small action certificates feed the actual pure-extension
completion and double-centralizer argument in `CommonCompletion`. They use
the existing ATLAS action and do not assume that the whole normalizer
preserves the original kernel or any selected lift.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

set_option Elab.async false
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

private theorem mask_bound : ∀ j : Fin 32, displacementMask 0 0 j < 2048 := by decide +kernel
private theorem mask_zero : displacementMask 0 0 0 = 0 := rfl
private theorem mask_xor : ∀ i j : Fin 32,
    displacementMask 0 0 i ^^^ displacementMask 0 0 j =
      displacementMask 0 0 ⟨i.val ^^^ j.val,Nat.xor_lt_two_pow (n := 5) i.isLt j.isLt⟩ := by decide +kernel

/-- The common displacement space in the original binary kernel. -/
@[expose] def commonKernel : Subgroup M where
  carrier := {u | ∃ j : Fin 32, u = kernelValue (displacementMask 0 0 j)}
  one_mem' := ⟨0,by rw [mask_zero,kernelValue_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨⟨i.val ^^^ j.val,Nat.xor_lt_two_pow (n := 5) i.isLt j.isLt⟩,by
      rw [← kernelValue_xor]
      exact congrArg kernelValue (by simpa only [Nat.xor_eq] using mask_xor i j)⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨i,inv_eq_of_mul_eq_one_left (kernelValue_square _)⟩

@[expose] def commonSpace : Subgroup Model := commonKernel.map M.subtype

theorem commonKernel_le : commonKernel ≤ max1Kernel := by
  rintro _ ⟨i,rfl⟩
  exact (maskValue matrixA_mul_self matrixB_pow_four _).property

theorem commonSpace_le_kernel : commonSpace ≤ embeddedKernel := map_mono commonKernel_le

theorem mem_commonSpace (v : Model) : v ∈ commonSpace ↔
    ∃ i : Fin 32, v = (kernelValue (displacementMask 0 0 i) : Model) := by
  constructor
  · rintro ⟨u,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩; exact mem_map_of_mem M.subtype (show _ ∈ commonKernel from ⟨i,rfl⟩)

theorem commonSpace_card : Nat.card commonSpace = 32 := by
  let f : Fin 32 → commonKernel := fun j => ⟨kernelValue (displacementMask 0 0 j),j,rfl⟩
  have hi : Function.Injective f := by
    intro i j h
    exact displacement_injective 0 0 (kernelValue_injective (mask_bound i) (mask_bound j)
      (congrArg (fun u : commonKernel => (u : M)) h))
  have hs : Function.Surjective f := by
    rintro ⟨u,i,rfl⟩; exact ⟨i,rfl⟩
  rw [commonSpace,card_map_of_injective M.subtype_injective,
    ← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_fin]

theorem nativePair_le_commonSpace : nativePair ≤ commonSpace := by
  apply (closure_le _).mpr
  rintro v (rfl | rfl)
  · exact (mem_commonSpace _).mpr ⟨15,rfl⟩
  · exact (mem_commonSpace _).mpr ⟨20,rfl⟩

private theorem common_fixed : ∀ (i : Fin 3) (j : Fin 32),
    SylowCore.starMask (element (pureIndex 1 i)) (displacementMask 0 0 j) =
      displacementMask 0 0 j := by decide +kernel

private theorem common_fixed_only : ∀ m : Fin 2048,
    SylowCore.starMask (element 12) m.val = m.val →
    SylowCore.starMask (element 57) m.val = m.val →
    ∃ j : Fin 32, m.val = displacementMask 0 0 j := by decide +kernel

private theorem common_image_only : ∀ i : Fin 96,
    SylowCore.starMask (element i) 3 = 3 →
    SylowCore.starMask (element i) 25 = 25 →
    SylowCore.starMask (element i) 320 = 320 →
    SylowCore.starMask (element i) 616 = 616 →
    SylowCore.starMask (element i) 1257 = 1257 →
    i = 0 ∨ i = 12 ∨ i = 57 ∨ i = 79 := by decide +kernel



private theorem commute_kernel_iff (z : M) (m : Fin 2048) :
    Commute z (kernelValue m.val) ↔ SylowCore.starMask (starHom z) m.val = m.val := by
  constructor
  · intro h
    have he : z * kernelValue m.val * z⁻¹ = kernelValue m.val := by
      rw [h.eq,mul_inv_cancel_right]
    rw [kernel_conjugation] at he
    exact kernelValue_injective (SylowCore.Transport.starMask_lt _ _) m.isLt he
  · intro h
    have he := kernel_conjugation z m.val
    change z * kernelValue m.val * z⁻¹ = kernelValue (SylowCore.starMask (starHom z) m.val) at he
    rw [h] at he
    exact mul_inv_eq_iff_eq_mul.mp he

theorem commonSpace_centralized (z : M) (hz : starHom z ∈ pureBlock 1) :
    (z : Model) ∈ centralizer (commonSpace : Set Model) := by
  have hfix : ∀ j : Fin 32, SylowCore.starMask (starHom z) (displacementMask 0 0 j) =
      displacementMask 0 0 j := by
    have hp : ∀ p ∈ pureBlock 1, ∀ j : Fin 32,
        SylowCore.starMask p (displacementMask 0 0 j) = displacementMask 0 0 j := by
      intro p hp
      -- Work in the subgroup fixing the displayed kernel elements.
      let B := (centralizer (commonKernel : Set M)).map starHom
      have hle : pureBlock 1 ≤ B := by
        apply (closure_le _).mpr
        rintro _ ⟨i,rfl⟩
        obtain ⟨u,hu⟩ := starHom_surjective (element (pureIndex 1 i.castSucc))
        refine ⟨u,?_,hu⟩
        rintro v ⟨j,rfl⟩
        exact ((commute_kernel_iff u ⟨_,mask_bound j⟩).mpr
          (hu.symm ▸ common_fixed i.castSucc j)).eq.symm
      obtain ⟨u,hu,he⟩ := hle hp
      intro j
      rw [← he]
      apply (commute_kernel_iff u ⟨_,mask_bound j⟩).mp
      exact (show Commute (kernelValue (displacementMask 0 0 j)) u from hu _ ⟨j,rfl⟩).symm
    exact hp _ hz
  intro v hv
  obtain ⟨j,rfl⟩ := (mem_commonSpace v).mp hv
  exact congrArg (fun u : M => (u : Model))
    ((commute_kernel_iff z ⟨_,mask_bound j⟩).mpr (hfix j)).eq.symm

/-- The pointwise stabilizer of the common space in the actual pair image
is precisely the common four-group. -/
theorem commonSpace_centralizer_image (z : M)
    (hp : (z : Model) ∈ centralizer (nativePair : Set Model))
    (hc : (z : Model) ∈ centralizer (commonSpace : Set Model)) :
    starHom z ∈ pureBlock 1 := by
  have hp' : z ∈ localPairCentralizer := by
    rintro v (rfl | rfl)
    · exact Subtype.ext (hp _ (subset_closure (by simp)))
    · exact Subtype.ext (hp _ (subset_closure (by simp)))
  obtain ⟨i,hi⟩ := (mem_pair_image_iff (starHom z)).mp (mem_map_of_mem starHom hp')
  have hf (j : Fin 32) : SylowCore.starMask (element i) (displacementMask 0 0 j) =
      displacementMask 0 0 j := by
    rw [hi]
    apply (commute_kernel_iff z ⟨_,mask_bound j⟩).mp
    exact (show Commute (kernelValue (displacementMask 0 0 j)) z from
      Subtype.ext (hc _ ((mem_commonSpace _).mpr ⟨j,rfl⟩))).symm
  rw [← hi]
  rcases common_image_only i (hf 1) (hf 2) (hf 4) (hf 8) (hf 16) with rfl | rfl | rfl | rfl
  · have he : element 0 = 1 := by apply Subtype.ext; decide +kernel
    exact he ▸ (pureBlock 1).one_mem
  · exact pureIndex_mem 1 0
  · exact pureIndex_mem 1 1
  · exact pureIndex_mem 1 2

/-- Exact common kernel of a subgroup with full common four-image. -/
theorem common_centralizer_kernel (X : Subgroup Model)
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map starHom = pureBlock 1) :
    centralizer (X : Set Model) ⊓ embeddedKernel = commonSpace := by
  apply le_antisymm
  · rintro v ⟨hv,u,hu,rfl⟩
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
    have he : kernelValue m.val = u := congrArg Subtype.val hm
    have hfix (i : Fin 3) : SylowCore.starMask (element (pureIndex 1 i)) m.val = m.val := by
      obtain ⟨z,hz,hzq⟩ := himage.symm ▸ pureIndex_mem 1 i
      rw [← hzq]
      apply (commute_kernel_iff z m).mp
      exact Subtype.ext (he.symm ▸ hv _ hz)
    obtain ⟨j,hj⟩ := common_fixed_only m (hfix 0) (hfix 1)
    apply (mem_commonSpace _).mpr
    exact ⟨j,congrArg (fun u : M => (u : Model)) (he.symm.trans (congrArg kernelValue hj))⟩
  · intro v hv
    refine ⟨?_,commonSpace_le_kernel hv⟩
    intro z hz
    let u : M := ⟨z,hXM hz⟩
    have hu : starHom u ∈ pureBlock 1 := himage ▸ mem_map_of_mem starHom hz
    exact (commonSpace_centralized u hu v hv).symm


private def displacementPreimage : Fin 3 → Fin 32 → Fin 2048 := ![![0,1,40,41,64,65,104,105,233,232,193,192,169,168,129,128,97,96,73,72,33,32,9,8,136,137,160,161,200,201,224,225],![0,129,13,140,44,173,33,160,161,32,172,45,141,12,128,1,4,133,9,136,40,169,37,164,165,36,168,41,137,8,132,5],![0,128,37,165,9,137,44,172,45,173,8,136,36,164,1,129,4,132,33,161,13,141,40,168,41,169,12,140,32,160,5,133]]

private theorem displacement_preimage : ∀ (i : Fin 3) (j : Fin 32),
    SylowCore.starMask (element (pureIndex 1 i)) (displacementPreimage i j).val ^^^
      (displacementPreimage i j).val = displacementMask 0 0 j := by decide +kernel

/-- Every common-space element is a displacement of each of the three
nonidentity common-image elements. -/
theorem commonSpace_displacement (i : Fin 3) (d : M) (hd : d ∈ commonKernel) :
    ∃ n : Fin 2048, d = kernelValue
      (SylowCore.starMask (element (pureIndex 1 i)) n.val ^^^ n.val) := by
  obtain ⟨j,rfl⟩ := hd
  exact ⟨displacementPreimage i j,congrArg kernelValue (displacement_preimage i j).symm⟩

/-- All nonidentity elements of the common kernel are first-class involutions. -/
theorem commonSpace_pure (v : Model) (hv : v ∈ commonSpace) (hv1 : v ≠ 1) : IsConj a v := by
  obtain ⟨i,rfl⟩ := (mem_commonSpace v).mp hv
  let m := displacementMask 0 0 i
  have hm1 : kernelValue m ≠ 1 := fun he => hv1 (congrArg (fun u : M => (u : Model)) he)
  have hm0 : m ≠ 0 := by
    intro h; exact hm1 (h ▸ kernelValue_zero)
  have hn : ∀ u v : Fin 24, pairLabel u v ≠ m := by
    have hh : ∀ i : Fin 32, displacementMask 0 0 i ≠ 0 →
        ∀ u v : Fin 24, pairLabel u v ≠ displacementMask 0 0 i := by decide +kernel
    exact hh i hm0
  obtain ⟨g, hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four
    (kernelValue m) (maskValue _ _ _).property hm1
  · have hback : g⁻¹ * kernelValue 1 * (g⁻¹)⁻¹ = kernelValue m := by
      rw [show kernelValue 1 = localKernelSeed matrixA_mul_self matrixB_pow_four from
        maskValue_one _ _,hg]
      simp [mul_assoc]
    have hp := congrArg Subtype.val (starHom_pair g⁻¹ 0 1)
    change g⁻¹ * kernelValue 1 * (g⁻¹)⁻¹ =
      kernelValue (pairLabel ((starHom g⁻¹).val 0) ((starHom g⁻¹).val 1)) at hp
    exact (hn _ _ (kernelValue_injective (pairLabel_lt _ _) (mask_bound i)
      (hp.symm.trans hback))).elim
  · obtain ⟨q,hq⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
    have hc : IsConj (kernelValue m : Model) (kernelPair matrixA_mul_self matrixB_pow_four : Model) :=
      M.subtype.map_isConj (isConj_iff.mpr ⟨g,hg.symm⟩)
    exact (hc.trans (isConj_iff.mpr ⟨q,hq.symm⟩)).symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
