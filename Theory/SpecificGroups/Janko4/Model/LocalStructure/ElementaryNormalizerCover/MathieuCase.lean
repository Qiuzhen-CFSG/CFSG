module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuUniqueness
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.KernelOrbits
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion.Seeds

/-!
# The Mathieu case of the native elementary-normalizer argument

The two native kernel orbits are the seed orbit and an orbit fusing to the
first involution class. A kernel involution outside the first class is therefore
conjugate to the seed by an element of max1. The full ambient seed-centralizer
bound then places its centralizer in max1. Kernel uniqueness consequently puts
the full normalizer of any subgroup of `E` containing such an involution in
max1, with no supplied centralizer or coverage premise.

This is the first case in Kleidman--Wilson (1988), Proposition 2.2.3, p.491.
The argument does not require the zero-form hypothesis once `X ≤ E` is known.
The native kernel orbit and ambient fusion certificates use the ATLAS max1 words.
-/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover
open Subgroup Cardinality Simplicity.Max1Fusion MathieuSeedCentralizer
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localKernelSeed

/-- The full centralizer of a nonfirst-class kernel element lies in literal max1. -/
theorem kernel_nonfirst_centralizer_le_max1 (t : Model) (htE : t ∈ embeddedKernel)
    (ht1 : t ≠ 1) (hnt : ¬ IsConj Janko4.a t) :
    centralizer ({t} : Set Model) ≤ max1 := by
  obtain ⟨z,hz,rfl⟩ := htE
  have hz1 : z ≠ 1 := fun he => ht1 (congrArg Subtype.val he)
  obtain ⟨g,hg | hg⟩ := kernel_nonidentity_orbits matrixA_mul_self matrixB_pow_four z hz hz1
  · have hc := map_centralizer_le_centralizer_image ({(z : Model)} : Set Model)
      (MulAut.conj (g : Model)).toMonoidHom
    rw [Set.image_singleton] at hc
    change (centralizer ({(z : Model)} : Set Model)).map
        (MulAut.conj (g : Model)).toMonoidHom ≤
      centralizer ({(MulAut.conj (g : Model)) (z : Model)} : Set Model) at hc
    have he : (MulAut.conj (g : Model)) (z : Model) =
        (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) :=
      congrArg Subtype.val hg.symm
    rw [he] at hc
    have hseed := ambientSeedCentralizer_le_max1_of_card_le
      matrixA_mul_self matrixB_pow_four ambientSeedCentralizer_card_le
    have hmap := hc.trans hseed
    intro c hcz
    have hcM : (MulAut.conj (g : Model)) c ∈ max1 := hmap ⟨c,hcz,rfl⟩
    have hm := max1.mul_mem (max1.mul_mem (max1.inv_mem g.property) hcM) g.property
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using hm
  · have hzp : IsConj (z : Model) (kernelPair matrixA_mul_self matrixB_pow_four : Model) :=
      max1.subtype.map_isConj (isConj_iff.mpr ⟨g,hg.symm⟩)
    obtain ⟨q,hq⟩ := pair_fuses_first matrixA_mul_self matrixB_pow_four
    have hpa : IsConj (kernelPair matrixA_mul_self matrixB_pow_four : Model) Janko4.a :=
      isConj_iff.mpr ⟨q,hq.symm⟩
    exact (hnt (hzp.trans hpa).symm).elim

/-- An actual nonfirst involution in `X ≤ E` supplies the source centralizer placement. -/
theorem kernel_subgroup_centralizer_le_max1 (X : Subgroup Model) (hXE : X ≤ embeddedKernel)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    centralizer (X : Set Model) ≤ max1 := by
  have ht1 : t ≠ 1 := by
    intro he
    rw [he, orderOf_one] at ht2
    omega
  exact (centralizer_le (Set.singleton_subset_iff.mpr htX)).trans
    (kernel_nonfirst_centralizer_le_max1 t (hXE htX) ht1 hnt)

/-- The full Mathieu case of the normalizer argument, with its native class marking. -/
theorem normalizer_le_mathieu_of_nonfirst_kernel_involution
    (X : Subgroup Model) (hXE : X ≤ embeddedKernel)
    (t : Model) (htX : t ∈ X) (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    normalizer (X : Set Model) ≤ max1 :=
  normalizer_le_mathieu_of_kernel_and_centralizer X hXE
    (kernel_subgroup_centralizer_le_max1 X hXE t htX ht2 hnt)

/-- The Mathieu branch applied to an ambient radical, retaining the literal maps. -/
theorem radical_mathieu_local_of_nonfirst_kernel_involution
    (P X : Subgroup Model) (hP : P.IsPRadical 2)
    (hNX : normalizer (P : Set Model) ≤ normalizer (X : Set Model))
    (hXE : X ≤ embeddedKernel) (t : Model) (htX : t ∈ X)
    (ht2 : orderOf t = 2) (hnt : ¬ IsConj Janko4.a t) :
    normalizer (P : Set Model) ≤ max1 ∧ P ≤ max1 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).map max1.subtype =
        normalizer (P : Set Model) ∧
      (P.subgroupOf max1).IsPRadical 2 ∧
      (normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2 = P.subgroupOf max1 ∧
      ((normalizer (P.subgroupOf max1 : Set max1)).pCoreIn 2).map max1.subtype = P :=
  radical_mathieu_local_of_kernel_and_centralizer P X hP hNX hXE
    (kernel_subgroup_centralizer_le_max1 X hXE t htX ht2 hnt)

end Janko4.LocalStructure.ElementaryNormalizerCover
