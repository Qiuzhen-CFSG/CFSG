module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.BoxImages

/-!
# Canonical central enlargement for four residual box images

The four order-eight residual images have two tetrad orbits with the same native
kernel label, 818. Their point stabilizers force the full ambient centralizer
to fix that involution. If the central omega has the same quotient image, its
two relevant pair characters agree, placing 818 in its intrinsic form radical.
Otherwise the canonical enlargement has quotient order greater than eight.

These are the literal Figure 2(a) rows [16,1,2], [16,1,6], [16,2,9], and
[16,3,13], under the existing native marking. No printed AAA(2) centralizer
identification is used. The normalizer consumer is in BoxResidualApplication.
Source: Kleidman--Wilson (1988), Section 2.3, Figure 2(a), pp.490--493.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
open Cardinality QuotientCount.Image KernelCount
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open ElementaryEightGeometry M22Images.KernelAction BoxImages
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis

def largeRow (r : Fin 4) : Fin 8 := ⟨r.val+4,by omega⟩
def generator (r : Fin 8) : Fin 3 → StarGroup := spaceGenerator (r.castLE (by decide))
def element (r : Fin 8) (k : Fin 8) : StarGroup :=
  binaryProduct (generator r) (fun j => k.val.testBit j.val)

private theorem generator_square (r : Fin 8) (j : Fin 3) :
    generator r j * generator r j = 1 := by
  apply Subtype.ext
  revert r j
  decide +kernel
private theorem generator_commute (r : Fin 8) (i j : Fin 3) :
    Commute (generator r i) (generator r j) := by
  apply Subtype.ext
  revert r i j
  decide +kernel
private theorem binary_coordinates : ∀ v : Fin 3 → Bool,
    ∃ k : Fin 8, (fun j : Fin 3 => k.val.testBit j.val) = v := by decide +kernel

theorem element_mem (r : Fin 8) (k : Fin 8) : element r k ∈ residualImage r :=
  binaryProduct_mem _ _ _ (fun j => subset_closure (Set.mem_range_self j))

theorem mem_residual_iff (r : Fin 8) (p : StarGroup) :
    p ∈ residualImage r ↔ ∃ k : Fin 8, element r k = p := by
  constructor
  · intro hp
    obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct (generator r)
      (generator_square r) (generator_commute r) p).mp hp
    obtain ⟨k,hk⟩ := binary_coordinates v
    exact ⟨k,by rw [element,hk]⟩
  · rintro ⟨k,rfl⟩
    exact element_mem r k

theorem residual_card_le (r : Fin 8) : Nat.card (residualImage r) ≤ 8 := by
  let f : Fin 8 → residualImage r := fun k => ⟨element r k,element_mem r k⟩
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨k,hk⟩ := (mem_residual_iff r p).mp p.property
    exact ⟨k,Subtype.ext hk⟩
  simpa using Nat.card_le_card_of_surjective f hf

private theorem large_injective : ∀ r : Fin 4,
    Function.Injective (fun k : Fin 8 => (element (largeRow r) k).val) := by decide +kernel

theorem large_card (r : Fin 4) : Nat.card (residualImage (largeRow r)) = 8 := by
  apply le_antisymm (residual_card_le _)
  let f : Fin 8 → residualImage (largeRow r) := fun k => ⟨element _ k,element_mem _ k⟩
  have hf : Function.Injective f := by
    intro i j h
    exact large_injective r (congrArg (fun p : residualImage (largeRow r) => p.val.val) h)
  simpa using Nat.card_le_card_of_injective f hf

private def basePoint : Fin 4 → Fin 24 := ![4,2,6,2]
private def orbitWord : Fin 4 → Fin 4 → Fin 8 := ![![0,2,4,6],![0,1,4,5],![0,1,4,5],![0,1,4,5]]
private def tetrad (r : Fin 4) (j : Fin 4) : Fin 24 :=
  (element (largeRow r) (orbitWord r j)).val (basePoint r)
private theorem orbit_label : ∀ (r : Fin 4) (y : Fin 24),
    (∀ k : Fin 8, (element (largeRow r) k).val y = y ↔
      (element (largeRow r) k).val (basePoint r) = basePoint r) →
    Nat.xor
      (pairLabel ((element (largeRow r) (orbitWord r 0)).val y)
        ((element (largeRow r) (orbitWord r 1)).val y))
      (pairLabel ((element (largeRow r) (orbitWord r 2)).val y)
        ((element (largeRow r) (orbitWord r 3)).val y)) = 818 := by decide +kernel

private theorem tetrad_product (r : Fin 4) : kernelValue 818 =
    kernelValue (pairLabel (tetrad r 0) (tetrad r 1)) *
      kernelValue (pairLabel (tetrad r 2) (tetrad r 3)) := by
  rw [← kernelValue_xor]
  exact congrArg kernelValue (orbit_label r (basePoint r) (fun _ => Iff.rfl)).symm

theorem centralInvolution_mem_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (r : Fin 4) (hrow : (X.subgroupOf M).map starHom = residualImage (largeRow r))
    (hCM : centralizer (X : Set Model) ≤ M) :
    NonsingularC.centralInvolution ∈ omegaCenterIn (centralizer (X : Set Model)) := by
  have hcomm (c : Model) (hc : c ∈ centralizer (X : Set Model)) :
      c * NonsingularC.centralInvolution = NonsingularC.centralInvolution * c := by
    let c0 : M := ⟨c,hCM hc⟩
    have hact (k : Fin 8) (j : Fin 24) :
        (starHom c0).val ((element (largeRow r) k).val j) =
          (element (largeRow r) k).val ((starHom c0).val j) := by
      obtain ⟨x,hx,hxk⟩ := hrow ▸ element_mem (largeRow r) k
      have hh : Commute c0 x := Subtype.ext (hc x hx).symm
      have he := congrArg (fun p : StarGroup => p.val j) (hh.map starHom).eq
      simpa only [hxk,coe_mul,Equiv.Perm.mul_apply] using he
    have hstab (k : Fin 8) :
        (element (largeRow r) k).val ((starHom c0).val (basePoint r)) =
            (starHom c0).val (basePoint r) ↔
          (element (largeRow r) k).val (basePoint r) = basePoint r := by
      rw [← hact]
      exact (starHom c0).val.injective.eq_iff
    have he : c0 * kernelValue 818 * c0⁻¹ = kernelValue 818 := by
      rw [tetrad_product r]
      change (MulAut.conj c0).toMonoidHom (_ * _) = _
      rw [map_mul]
      change (c0 * _ * c0⁻¹) * (c0 * _ * c0⁻¹) = _
      rw [show c0 * kernelValue (pairLabel (tetrad r 0) (tetrad r 1)) * c0⁻¹ =
        kernelValue (pairLabel ((starHom c0).val (tetrad r 0)) ((starHom c0).val (tetrad r 1))) from
        congrArg Subtype.val (starHom_pair c0 (tetrad r 0) (tetrad r 1))]
      rw [show c0 * kernelValue (pairLabel (tetrad r 2) (tetrad r 3)) * c0⁻¹ =
        kernelValue (pairLabel ((starHom c0).val (tetrad r 2)) ((starHom c0).val (tetrad r 3))) from
        congrArg Subtype.val (starHom_pair c0 (tetrad r 2) (tetrad r 3))]
      simp only [tetrad,hact]
      rw [← kernelValue_xor,orbit_label r _ hstab]
      exact tetrad_product r
    exact congrArg (fun y : M => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨fun x hx => hcomm x (X.le_centralizer hx),hcomm,by
      rw [← NonsingularC.centralInvolution_order]; exact pow_orderOf_eq_one _⟩

private theorem pair_action : ∀ (r : Fin 4) (k : Fin 8),
    let p := (element (largeRow r) k).val
    (p 0 = 0 ∧ p 1 = 1 ∧ p 11 = 11 ∧ p 12 = 12) ∨
      (p 0 = 1 ∧ p 1 = 0 ∧ p 11 = 12 ∧ p 12 = 11) := by decide +kernel

private theorem pair_inner_iff (r : Fin 4) (w : M)
    (hw : starHom w ∈ residualImage (largeRow r)) :
    InnerRelated (kernelValue 1 : Model) (w : Model) ↔
      InnerRelated (kernelValue 819 : Model) (w : Model) := by
  obtain ⟨k,hk⟩ := (mem_residual_iff _ _).mp hw
  rcases pair_action r k with ⟨h0,h1,h11,h12⟩ | ⟨h0,h1,h11,h12⟩
  · rw [hk] at h0 h1 h11 h12
    exact iff_of_true (inner_of_star_fixed w 0 1 (by decide) h0 h1)
      (inner_of_star_fixed w 11 12 (by decide) h11 h12)
  · rw [hk] at h0 h1 h11 h12
    exact iff_of_false (LinearFive.Geometry.not_inner_of_star_swap w 0 1 (by decide) h0 h1)
      (LinearFive.Geometry.not_inner_of_star_swap w 11 12 (by decide) h11 h12)

private theorem pair_fixed (r : Fin 4) (j : Fin 3) (m : Fin 2) :
    SylowCore.starMask (generator (largeRow r) j) (![1,819] m) = ![1,819] m := by
  revert r j m
  decide +kernel

private theorem pair_centralizes (X : Subgroup Model) (hXM : X ≤ M)
    (r : Fin 4) (hrow : (X.subgroupOf M).map starHom = residualImage (largeRow r))
    (m : Fin 2) : (kernelValue (![1,819] m) : Model) ∈ centralizer (X : Set Model) := by
  have hf := (starMask_closure_fixed_iff (generator (largeRow r))
    (⟨![1,819] m,by fin_cases m <;> decide⟩ : Fin 2048)).mpr (fun j => pair_fixed r j m)
  intro x hx
  let x0 : M := ⟨x,hXM hx⟩
  have he := kernel_conjugation x0 (![1,819] m)
  change x0 * kernelValue (![1,819] m) * x0⁻¹ =
    kernelValue (SylowCore.starMask (starHom x0) (![1,819] m)) at he
  have hm : starHom x0 ∈ residualImage (largeRow r) :=
    hrow ▸ mem_map_of_mem starHom (show x0 ∈ X.subgroupOf M from hx)
  rw [hf _ hm] at he
  exact congrArg (fun y : M => (y : Model)) (mul_inv_eq_iff_eq_mul.mp he)

theorem centralInvolution_mem_radical_of_omega_image_le
    (X : Subgroup Model) [IsElementaryAbelian 2 X] (hXM : X ≤ M)
    (r : Fin 4) (hrow : (X.subgroupOf M).map starHom = residualImage (largeRow r))
    (hCM : centralizer (X : Set Model) ≤ M)
    (him : ((omegaCenterIn (centralizer (X : Set Model))).subgroupOf M).map starHom ≤
      residualImage (largeRow r)) : NonsingularC.centralInvolution ∈ NonsingularC.zeroWitness X := by
  have ht := centralInvolution_mem_omega X r hrow hCM
  refine ⟨ht,?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1,outerValue_one_right]
  let w0 : M := ⟨w,hCM (map_subtype_le _ hw)⟩
  have hw2 : orderOf w = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) w hw) hw1
  have hc (m : Fin 2) : Commute (kernelValue (![1,819] m) : Model) w :=
    ((mem_omegaCenterIn_iff _ _).mp hw).2.1 _ (pair_centralizes X hXM r hrow m)
  have ho0 : orderOf (kernelValue 1 : Model) = 2 := pair_order 0 1 (by decide)
  have ho1 : orderOf (kernelValue 819 : Model) = 2 := pair_order 11 12 (by decide)
  have hi := pair_inner_iff r w0 (him (mem_map_of_mem starHom hw))
  have he : InnerRelated w (kernelValue 1 : Model) ↔ InnerRelated w (kernelValue 819 : Model) :=
    (innerRelated_symm _ _ ho0 hw2 (hc 0)).symm.trans
      (hi.trans (innerRelated_symm _ _ ho1 hw2 (hc 1)))
  have hv : outerValue w (kernelValue 1 : Model) = outerValue w (kernelValue 819 : Model) := by
    simp only [outerValue,hw1,false_or]
    rw [he]
  have hprod : NonsingularC.centralInvolution =
      (kernelValue 1 : Model) * (kernelValue 819 : Model) := by
    change (kernelValue 818 : Model) = ((kernelValue 1 * kernelValue 819 : M) : Model)
    rw [← kernelValue_xor]
    rfl
  have hc0 : Commute w (kernelValue 1 : Model) := (hc 0).symm
  have hc1 : Commute w (kernelValue 819 : Model) := (hc 1).symm
  have hz : outerValue w NonsingularC.centralInvolution = 0 := by
    rw [hprod,outerValue_mul_right w hw2 _ _ hc0 hc1,hv,← two_mul]
    rw [show (2 : ZMod 2) = 0 from rfl,zero_mul]
  exact (outerValue_eq_zero_iff _ _ NonsingularC.centralInvolution_ne_one).mpr
    ((innerRelated_symm _ _ hw2 NonsingularC.centralInvolution_order
      (setLike_mul_comm hw ht)).mp ((outerValue_eq_zero_iff _ _ hw1).mp hz))


theorem source_radical_or_large_omega (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hs : (seed : Model) ∈ X) (r : Fin 4)
    (hrow : (X.subgroupOf M).map starHom = residualImage (largeRow r)) :
    NonsingularC.zeroWitness X ≠ ⊥ ∨
      8 < Nat.card (((omegaCenterIn (centralizer (X : Set Model))).subgroupOf M).map starHom) := by
  have hCM : centralizer (X : Set Model) ≤ M :=
    (centralizer_le (Set.singleton_subset_iff.mpr hs)).trans ambient_le_max1
  by_cases hlarge : 8 < Nat.card (((omegaCenterIn (centralizer (X : Set Model))).subgroupOf M).map starHom)
  · exact Or.inr hlarge
  left
  have hle : residualImage (largeRow r) ≤
      ((omegaCenterIn (centralizer (X : Set Model))).subgroupOf M).map starHom := by
    rw [← hrow]
    exact map_mono (fun x hx => elementary_le_centralizer_omegaCenter X hx)
  have he := eq_of_le_of_card_ge hle (by rw [large_card]; omega)
  have ht := centralInvolution_mem_radical_of_omega_image_le X (X.le_centralizer.trans hCM)
    r hrow hCM he.ge
  exact fun hz => NonsingularC.centralInvolution_ne_one (mem_bot.mp (hz ▸ ht))

end Janko4.LocalStructure.ElementaryNormalizerCover.BoxResidual
