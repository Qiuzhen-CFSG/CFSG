module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.TwoImagePlacement
import Mathlib.Tactic.Group

/-!
# Simultaneous normalization of exceptional actual lifts

Once two pure elementary extensions with the exceptional four-image share
one first lift, their second lifts differ by the native pair. The difference
lies in the displacement spaces of both the second image and the product
image, whose intersection is exactly that pair. Kernel conjugation can first
align the first lifts, so all actual exceptional extensions are conjugate by
the original binary kernel, with their full centralizers and normalizers
transported by the same element.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open ElementaryEightGeometry NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis localX localY
set_option backward.isDefEq.respectTransparency true


private theorem pure_image_ne_one (r : Fin 2) (i : Fin 3) :
    element (pureIndex r i) ≠ 1 := by
  intro he
  have h := congrArg (fun p : StarGroup => p.val 0) he
  have hn : ∀ (r : Fin 2) (i : Fin 3), (element (pureIndex r i)).val 0 ≠ 0 := by decide +kernel
  exact hn r i h

/-- The difference between an actual first-class lift and any first-class
lift of its image lies in the corresponding displacement space. -/
theorem first_lift_difference (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (r : Fin 2) (i : Fin 3) (z t : M) (hz : (z : Model) ∈ X)
    (hzq : starHom z = element (pureIndex r i))
    (ht : IsConj a (t : Model)) (htq : starHom t = starHom z) :
    ∃ j : Fin 32, z⁻¹ * t = kernelValue (displacementMask r i j) := by
  have hzk : z ∉ max1Kernel := by
    intro hk
    exact pure_image_ne_one r i (hzq.symm.trans (MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hk)))
  obtain ⟨u,hu,he⟩ := pure_extension_lift_fiber_transitive X hpair hpure z hz hzk t ht htq
  obtain ⟨n,hn⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
  have hnu : kernelValue n.val = u := congrArg Subtype.val hn
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : Model) hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz2
  have hui : u⁻¹ = u := hnu ▸ inv_eq_of_mul_eq_one_left (kernelValue_square _)
  obtain ⟨j,hj⟩ := displacement_coordinates r i n
  have hc := kernel_conjugation z n.val
  change z * kernelValue n.val * z⁻¹ = kernelValue (SylowCore.starMask (starHom z) n.val) at hc
  rw [hnu,hzq,hzi] at hc
  refine ⟨j,?_⟩
  rw [← he]
  change z⁻¹ * (u * z * u⁻¹) = _
  rw [hzi,hui,← mul_assoc,← mul_assoc,hc,← hnu,← kernelValue_xor]
  exact congrArg kernelValue (by simpa only [Nat.xor_eq] using hj)

/-- Purity of the second lift and of its product with the first lift forces
it into the original subgroup. This is an exhaustive actual-fiber statement. -/
theorem exceptional_second_lift_mem (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (z t s : M) (hz : (z : Model) ∈ X) (ht : (t : Model) ∈ X)
    (hzq : starHom z = element 12) (htq : starHom t = element 64)
    (hsq : starHom s = element 64)
    (hs : IsConj a (s : Model)) (hzs : IsConj a ((z*s : M) : Model)) :
    (s : Model) ∈ X := by
  have hprod : element 12 * element 64 = element 88 := by
    apply Subtype.ext
    decide +kernel
  obtain ⟨i,hi⟩ := first_lift_difference X hpair hpure 0 1 t s ht htq hs (hsq.trans htq.symm)
  have hztq : starHom (z*t) = element 88 := by rw [map_mul,hzq,htq,hprod]
  have hzsq : starHom (z*s) = starHom (z*t) := by rw [map_mul,map_mul,hsq,htq]
  obtain ⟨j,hj⟩ := first_lift_difference X hpair hpure 0 2 (z*t) (z*s)
    (X.mul_mem hz ht) hztq hzs hzsq
  have hj' : t⁻¹*s = kernelValue (displacementMask 0 2 j) := by
    simpa only [mul_inv_rev,mul_assoc,inv_mul_cancel_left] using hj
  have hb : ∀ (r : Fin 2) (i : Fin 3) (j : Fin 32), displacementMask r i j < 2048 := by decide +kernel
  have hm := kernelValue_injective (hb 0 1 i) (hb 0 2 j) (hi.symm.trans hj')
  have hmask := exceptional_intersection 1 2 i j (by decide) hm
  have hd : ((t⁻¹*s : M) : Model) ∈ nativePair := by
    rw [hi]
    rcases hmask with h | h | h | h
    · rw [h,kernelValue_zero]; exact nativePair.one_mem
    · rw [h]; exact subset_closure (by simp)
    · rw [h]; exact subset_closure (by simp)
    · rw [h,show 1691 = Nat.xor 818 1449 from rfl,kernelValue_xor]
      exact nativePair.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have h := X.mul_mem ht (hpair hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using h

/-- Any two chosen actual lifts of the exceptional generators, together with
the native pair, generate the whole extension. -/
theorem exceptional_generated_by (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom = pureBlock 0)
    (z t : M) (hz : (z : Model) ∈ X) (ht : (t : Model) ∈ X)
    (hzq : starHom z = element 12) (htq : starHom t = element 64) :
    X = nativePair ⊔ closure ({(z : Model),(t : Model)} : Set Model) := by
  have hk := exceptional_kernel_eq_pair X hpair hpure 0 1 (by decide)
    (himage.symm ▸ pureIndex_mem 0 0) (himage.symm ▸ pureIndex_mem 0 1)
  have hXM := (elementary_overgroup_placement X hpair).1
  let A := nativePair ⊔ closure ({(z : Model),(t : Model)} : Set Model)
  have hzA : (z : Model) ∈ A := mem_sup_right (subset_closure (by simp))
  have htA : (t : Model) ∈ A := mem_sup_right (subset_closure (by simp))
  have hAX : A ≤ X := sup_le hpair ((closure_le _).mpr (by
    rintro v (rfl | rfl)
    · exact hz
    · exact ht))
  have hmap : (X.subgroupOf M).map starHom ≤ (A.subgroupOf M).map starHom := by
    rw [himage]
    apply (closure_le _).mpr
    rintro p ⟨j,rfl⟩
    fin_cases j
    · exact ⟨z,hzA,hzq⟩
    · exact ⟨t,htA,htq⟩
  apply le_antisymm ?_ hAX
  intro v hv
  let w : M := ⟨v,hXM hv⟩
  obtain ⟨u,hu,he⟩ := hmap (mem_map_of_mem starHom (show w ∈ X.subgroupOf M from hv))
  have hd : w * u⁻¹ ∈ max1Kernel := by
    rw [← starHom_ker]
    apply MonoidHom.mem_ker.mpr
    rw [map_mul,map_inv,he,mul_inv_cancel]
  have hD : ((w * u⁻¹ : M) : Model) ∈ nativePair := by
    rw [← hk]
    exact ⟨X.mul_mem hv (X.inv_mem (hAX hu)), mem_map_of_mem M.subtype hd⟩
  have hmem := A.mul_mem (mem_sup_left hD) hu
  change ((w : Model) * (u : Model)⁻¹) * (u : Model) ∈ A at hmem
  simpa only [inv_mul_cancel_right] using hmem

/-- Equality follows from sharing just one first lift; there is no assumption
that either whole normalizer preserves the chosen lift. -/
theorem exceptional_eq_of_common_first (X Y : Subgroup Model)
    [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Y]
    (hPX : nativePair ≤ X) (hPY : nativePair ≤ Y)
    (hpX : ∀ v ∈ X, v ≠ 1 → IsConj a v) (hpY : ∀ v ∈ Y, v ≠ 1 → IsConj a v)
    (hqX : (X.subgroupOf M).map starHom = pureBlock 0)
    (hqY : (Y.subgroupOf M).map starHom = pureBlock 0)
    (z : M) (hzX : (z : Model) ∈ X) (hzY : (z : Model) ∈ Y)
    (hzq : starHom z = element 12) : X = Y := by
  have direction (A B : Subgroup Model) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
      (hPA : nativePair ≤ A) (hPB : nativePair ≤ B)
      (hpA : ∀ v ∈ A, v ≠ 1 → IsConj a v) (hpB : ∀ v ∈ B, v ≠ 1 → IsConj a v)
      (hqA : (A.subgroupOf M).map starHom = pureBlock 0)
      (hqB : (B.subgroupOf M).map starHom = pureBlock 0)
      (hzA : (z : Model) ∈ A) (hzB : (z : Model) ∈ B) : B ≤ A := by
    obtain ⟨t,ht,htq⟩ := hqA.symm ▸ pureIndex_mem 0 1
    obtain ⟨s,hs,hsq⟩ := hqB.symm ▸ pureIndex_mem 0 1
    have hs1 : (s : Model) ≠ 1 := by
      intro he
      have he' : s = 1 := Subtype.ext he
      exact pure_image_ne_one 0 1 (hsq.symm.trans (by rw [he',map_one]))
    have hzs1 : ((z*s : M) : Model) ≠ 1 := by
      intro he
      have he' : z*s = 1 := Subtype.ext he
      have hprod : element 12 * element 64 = element 88 := by apply Subtype.ext; decide +kernel
      apply pure_image_ne_one 0 2
      calc
        element 88 = starHom (z*s) := by rw [map_mul,hzq,hsq]; exact hprod.symm
        _ = 1 := by rw [he',map_one]
    have hsA := exceptional_second_lift_mem A hPA hpA z t s hzA ht hzq htq hsq
      (hpB _ hs hs1) (hpB _ (B.mul_mem hzB hs) hzs1)
    rw [exceptional_generated_by B hPB hpB hqB z s hzB hs hzq hsq]
    exact sup_le hPA ((closure_le _).mpr (by rintro _ (rfl | rfl); exact hzA; exact hsA))
  exact le_antisymm (direction Y X hPY hPX hpY hpX hqY hqX hzY hzX)
    (direction X Y hPX hPY hpX hpY hqX hqY hzX hzY)

private theorem kernel_conjugation_image (X : Subgroup Model) (hXM : X ≤ M)
    (u : M) (hu : u ∈ max1Kernel) :
    ((X.map (MulAut.conj (u : Model)).toMonoidHom).subgroupOf M).map starHom =
      (X.subgroupOf M).map starHom := by
  have huq : starHom u = 1 := MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hu)
  apply le_antisymm
  · rintro q ⟨z,hz,rfl⟩
    obtain ⟨v,hv,hvz⟩ := hz
    let w : M := ⟨v,hXM hv⟩
    have he : (MulAut.conj u) w = z := Subtype.ext hvz
    have hq : starHom z = starHom w := by
      rw [← he]
      simp only [MulAut.conj_apply,map_mul,map_inv,huq,one_mul,inv_one,mul_one]
    rw [hq]
    exact mem_map_of_mem starHom hv
  · rintro q ⟨z,hz,rfl⟩
    refine ⟨(MulAut.conj u) z,mem_map_of_mem (MulAut.conj (u : Model)).toMonoidHom hz,?_⟩
    simp only [MulAut.conj_apply,map_mul,map_inv,huq,one_mul,inv_one,mul_one]

/-- The binary kernel acts transitively on the actual pure elementary
extensions with exceptional four-image. Both whole ambient local groups
are transported by that same kernel element. -/
theorem exceptional_kernel_transitive (X Y : Subgroup Model)
    [IsElementaryAbelian 2 X] [IsElementaryAbelian 2 Y]
    (hPX : nativePair ≤ X) (hPY : nativePair ≤ Y)
    (hpX : ∀ v ∈ X, v ≠ 1 → IsConj a v) (hpY : ∀ v ∈ Y, v ≠ 1 → IsConj a v)
    (hqX : (X.subgroupOf M).map starHom = pureBlock 0)
    (hqY : (Y.subgroupOf M).map starHom = pureBlock 0) :
    ∃ u ∈ max1Kernel, X.map (MulAut.conj (u : Model)).toMonoidHom = Y ∧
      (centralizer (X : Set Model)).map (MulAut.conj (u : Model)).toMonoidHom =
        centralizer (Y : Set Model) ∧
      (normalizer (X : Set Model)).map (MulAut.conj (u : Model)).toMonoidHom =
        normalizer (Y : Set Model) := by
  obtain ⟨z,hz,hzq⟩ := hqX.symm ▸ pureIndex_mem 0 0
  obtain ⟨t,ht,htq⟩ := hqY.symm ▸ pureIndex_mem 0 0
  have hzk : z ∉ max1Kernel := by
    intro hk
    exact pure_image_ne_one 0 0 (hzq.symm.trans (MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hk)))
  have ht1 : (t : Model) ≠ 1 := by
    intro he
    have he' : t = 1 := Subtype.ext he
    exact pure_image_ne_one 0 0 (htq.symm.trans (by rw [he',map_one]))
  obtain ⟨u,hu,he⟩ := pure_extension_lift_fiber_transitive X hPX hpX z hz hzk t
    (hpY _ ht ht1) (htq.trans hzq.symm)
  let Z := X.map (MulAut.conj (u : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
  have hPu : (u : Model) ∈ centralizer (nativePair : Set Model) := by
    obtain ⟨n,hn⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
    have hnu : kernelValue n.val = u := congrArg Subtype.val hn
    rw [← hnu,nativePair,centralizer_closure]
    rintro v (rfl | rfl) <;>
      exact congrArg (fun v : M => (v : Model)) (kernelValue_commute _ _).eq
  have hPZ : nativePair ≤ Z := by
    intro v hv
    have hf : (MulAut.conj (u : Model)) v = v := by
      change (u : Model) * v * (u : Model)⁻¹ = v
      rw [← hPu v hv,mul_inv_cancel_right]
    exact hf ▸ mem_map_of_mem (MulAut.conj (u : Model)).toMonoidHom (hPX hv)
  have hpZ : ∀ v ∈ Z, v ≠ 1 → IsConj a v := by
    rintro v ⟨w,hw,rfl⟩ hv
    exact (hpX w hw (fun he => hv (by rw [he,map_one]))).trans
      (isConj_iff.mpr ⟨(u : Model),rfl⟩)
  have hqZ : (Z.subgroupOf M).map starHom = pureBlock 0 :=
    (kernel_conjugation_image X (elementary_overgroup_placement X hPX).1 u hu).trans hqX
  have htZ : (t : Model) ∈ Z :=
    (congrArg (fun v : M => (v : Model)) he) ▸ mem_map_of_mem
      (MulAut.conj (u : Model)).toMonoidHom hz
  have hZY := exceptional_eq_of_common_first Z Y hPZ hPY hpZ hpY hqZ hqY t htZ ht htq
  refine ⟨u,hu,hZY,?_,?_⟩
  · exact (map_centralizer_equiv (X : Set Model) (MulAut.conj (u : Model))).trans
      (congrArg (fun A : Subgroup Model => centralizer (A : Set Model)) hZY)
  · exact (map_equiv_normalizer_eq X (MulAut.conj (u : Model))).trans
      (congrArg (fun A : Subgroup Model => normalizer (A : Set Model)) hZY)

/-- The original exceptional branch has order sixteen, with its actual
kernel and quotient orders both four. -/
theorem exceptional_four_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) : Nat.card X = 16 := by
  have hXM := (elementary_overgroup_placement X hpair).1
  let H := X.subgroupOf M
  let f := starHom.subgroupMap H
  have he : f.ker.map (M.subtype.comp H.subtype) = nativePair := by
    rw [show f.ker = max1Kernel.subgroupOf H from (ker_subgroupMap H starHom).trans
      (congrArg (fun K : Subgroup M => K.subgroupOf H) starHom_ker)]
    rw [← map_map,subgroupOf_map_subtype]
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,map_subgroupOf_eq_of_le hXM]
    exact (inf_comm _ _).trans (exceptional_four_kernel X hpair hpure hpos hfour)
  have hkcard : Nat.card f.ker = 4 := by
    rw [← card_map_of_injective (f := M.subtype.comp H.subtype)
      (M.subtype_injective.comp H.subtype_injective),he,nativePair_card]
  have hc := f.ker.card_mul_index
  have hf : Function.Surjective f := starHom.subgroupMap_surjective H
  rw [index_ker,MonoidHom.range_eq_top_of_surjective f hf,card_top,hkcard] at hc
  change 4 * Nat.card (H.map starHom) = Nat.card H at hc
  rw [hfour] at hc
  have hcard : Nat.card H = Nat.card X := Nat.card_congr (subgroupOfEquivOfLe hXM).toEquiv
  rw [hcard] at hc
  exact hc.symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
