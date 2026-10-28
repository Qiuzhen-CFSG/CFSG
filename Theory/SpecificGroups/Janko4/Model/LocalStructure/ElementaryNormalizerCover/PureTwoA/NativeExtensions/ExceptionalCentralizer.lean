module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalKernel
import Mathlib.Tactic.Group

/-!
# Surjectivity onto the full exceptional centralizer image

An arbitrary lift of an image-centralizing element can be corrected by the
binary kernel to fix the first actual lift. Purity of the second lift and
its product then puts its remaining difference in the native pair. The four
explicit pair displacements are realized while fixing the first lift, so a
second kernel correction centralizes the entire actual subgroup. This proves
the centralizer image is the full order-sixteen container and its order is
exactly 256, without a matrix census of all lifts.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

set_option Elab.async false
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




private theorem image_commute (q : StarGroup) (hq : q ∈ imageBlock 0) (i : Fin 3) :
    Commute q (element (pureIndex 0 i)) := by
  obtain ⟨j,rfl⟩ := (mem_imageBlock_iff _ _).mp hq
  clear hq
  apply Subtype.ext
  revert j i
  decide +kernel

private theorem pair_kernel_mem (u : M) (hu : u ∈ max1Kernel) : u ∈ localPairCentralizer := by
  obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
  have he : kernelValue m.val = u := congrArg Subtype.val hm
  rw [← he]
  rintro v (rfl | rfl) <;> exact (kernelValue_commute _ _).eq

private def pairMask : Fin 4 → ℕ := ![0,818,1449,1691]
private theorem pair_coordinates (v : Model) (hv : v ∈ nativePair) :
    ∃ i : Fin 4, v = (kernelValue (pairMask i) : Model) := by
  have hm (i : Fin 4) : (kernelValue (pairMask i) : Model) ∈ nativePair := by
    fin_cases i
    · exact kernelValue_zero.symm ▸ nativePair.one_mem
    · change (kernelValue 818 : Model) ∈ nativePair
      exact subset_closure (by simp)
    · change (kernelValue 1449 : Model) ∈ nativePair
      exact subset_closure (by simp)
    · change (kernelValue 1691 : Model) ∈ nativePair
      rw [show 1691 = Nat.xor 818 1449 from rfl,kernelValue_xor]
      exact nativePair.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  let f : Fin 4 → nativePair := fun i => ⟨kernelValue (pairMask i),hm i⟩
  have hi : Function.Injective f := by
    intro i j he
    have hb : ∀ i : Fin 4, pairMask i < 2048 := by decide +kernel
    have hin : Function.Injective pairMask := by decide +kernel
    apply hin
    exact kernelValue_injective (hb i) (hb j) (Subtype.ext (congrArg (fun u : nativePair => (u : Model)) he))
  have hs := ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi,by rw [Nat.card_fin,nativePair_card]⟩).2
  obtain ⟨i,hi⟩ := hs ⟨v,hv⟩
  exact ⟨i,(congrArg Subtype.val hi).symm⟩

private def pairPreimage : Fin 4 → ℕ := ![0,3,25,26]
private theorem pair_preimage : ∀ i : Fin 4,
    SylowCore.starMask (element 12) (pairPreimage i) = pairPreimage i ∧
    (SylowCore.starMask (element 64) (pairPreimage i)) ^^^ pairPreimage i = pairMask i := by
  decide +kernel

private theorem projection_conjugate (g z : M) (hc : Commute (starHom g) (starHom z)) :
    starHom ((MulAut.conj g) z) = starHom z := by
  simp only [MulAut.conj_apply,map_mul,map_inv]
  rw [hc.eq,mul_inv_cancel_right]

private theorem pure_ne_one (i : Fin 3) : element (pureIndex 0 i) ≠ 1 := by
  intro he
  have hh := congrArg (fun p : StarGroup => p.val 0) he
  have hn : ∀ i : Fin 3, (element (pureIndex 0 i)).val 0 ≠ 0 := by decide +kernel
  exact hn i hh

private theorem conjugate_mul (g u z : M) :
    (MulAut.conj (g*u)) z = (MulAut.conj g) ((MulAut.conj u) z) := by
  simp only [MulAut.conj_apply,mul_inv_rev,mul_assoc]

/-- Every element in the full exceptional image has a lift in the entire
ambient centralizer, after two explicit binary-kernel corrections. -/
theorem exceptional_image_lifts (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4)
    (q : StarGroup) (hq : q ∈ imageBlock 0) :
    q ∈ ((centralizer (X : Set Model)).subgroupOf M).map starHom := by
  obtain ⟨z,t,hz,ht,hzq,htq,hgen,_⟩ := exceptional_four_actual_lifts X hpair hpure hpos hfour
  obtain ⟨g,hg,hgq⟩ := imageBlock_le 0 hq
  have hgqz : Commute (starHom g) (starHom z) := hgq.symm ▸ hzq.symm ▸ image_commute q hq 0
  have hzk : z ∉ max1Kernel := by
    intro hk
    exact pure_ne_one 0 (hzq.symm.trans (MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hk)))
  have hz1 : (z : Model) ≠ 1 := by
    intro he
    exact hzk ((Subtype.ext he : z = 1).symm ▸ max1Kernel.one_mem)
  have hpz := (hpure _ hz hz1).trans (isConj_iff.mpr ⟨(g⁻¹ : M),rfl⟩)
  have hbackq : starHom ((MulAut.conj g⁻¹) z) = starHom z := by
    apply projection_conjugate
    simpa only [map_inv] using hgqz.inv_left
  obtain ⟨u,hu,he⟩ := pure_extension_lift_fiber_transitive X hpair hpure z hz hzk
    ((MulAut.conj g⁻¹) z) hpz hbackq
  let h : M := g*u
  have hhq : starHom h = q := by
    change starHom (g*u) = q
    rw [map_mul,hgq,MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hu),mul_one]
  have hfix : (MulAut.conj h) z = z := by
    rw [show h = g*u from rfl,conjugate_mul,he]
    simp only [MulAut.conj_apply,inv_inv,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one]
  let s : M := (MulAut.conj h) t
  have hsq : starHom s = element 64 := by
    exact (projection_conjugate h t (hhq.symm ▸ htq.symm ▸ image_commute q hq 1)).trans htq
  have ht1 : (t : Model) ≠ 1 := by
    intro he
    exact pure_ne_one 1 (htq.symm.trans (by rw [show t = 1 from Subtype.ext he,map_one]))
  have hprod : element 12 * element 64 = element 88 := by apply Subtype.ext; decide +kernel
  have hzt1 : ((z*t : M) : Model) ≠ 1 := by
    intro he
    apply pure_ne_one 2
    calc
      element 88 = starHom (z*t) := by rw [map_mul,hzq,htq,hprod]
      _ = 1 := by rw [show z*t = 1 from Subtype.ext he,map_one]
  have hps : IsConj a (s : Model) :=
    (hpure _ ht ht1).trans (isConj_iff.mpr ⟨(h : Model),rfl⟩)
  have hzs : IsConj a ((z*s : M) : Model) := by
    have hh : (MulAut.conj h) (z*t) = z*s := by rw [map_mul,hfix]
    exact (hpure _ (X.mul_mem hz ht) hzt1).trans
      (isConj_iff.mpr ⟨(h : Model),congrArg (fun v : M => (v : Model)) hh⟩)
  have hs := exceptional_second_lift_mem X hpair hpure z t s hz ht hzq htq hsq hps hzs
  have hdE : t⁻¹*s ∈ max1Kernel := by
    rw [← starHom_ker]
    apply MonoidHom.mem_ker.mpr
    rw [map_mul,map_inv,htq,hsq,inv_mul_cancel]
  have hdP : ((t⁻¹*s : M) : Model) ∈ nativePair := by
    rw [← exceptional_four_kernel X hpair hpure hpos hfour]
    exact ⟨X.mul_mem (X.inv_mem ht) hs,mem_map_of_mem M.subtype hdE⟩
  obtain ⟨i,hi⟩ := pair_coordinates _ hdP
  have hi' : t⁻¹*s = kernelValue (pairMask i) := Subtype.ext hi
  let v : M := kernelValue (pairPreimage i)
  have hv : v ∈ max1Kernel := (maskValue _ _ _).property
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_left (kernelValue_square _)
  have ht2 : t*t = 1 := by
    apply Subtype.ext
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (t : Model) ht
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hdelta : t⁻¹*v*t*v⁻¹ = kernelValue (pairMask i) := by
    have hc := kernel_conjugation t (pairPreimage i)
    change t*v*t⁻¹ = kernelValue (SylowCore.starMask (starHom t) (pairPreimage i)) at hc
    rw [htq,hti] at hc
    rw [hti,hvi,hc,← kernelValue_xor]
    exact congrArg kernelValue (pair_preimage i).2
  have hvt : (MulAut.conj v) t = s := by
    calc
      _ = t * (t⁻¹*v*t*v⁻¹) := by change v*t*v⁻¹ = _; group
      _ = t*(t⁻¹*s) := by rw [hdelta,← hi']
      _ = s := mul_inv_cancel_left _ _
  have hvs : (MulAut.conj v) s = t := by
    rw [← hvt]
    simp only [MulAut.conj_apply,hvi,mul_assoc]
    rw [← mul_assoc v v,show v*v = 1 from kernelValue_square _,one_mul,
      mul_one]
  have hvz : (MulAut.conj v) z = z := by
    have hc := kernel_conjugation z (pairPreimage i)
    change z*v*z⁻¹ = kernelValue (SylowCore.starMask (starHom z) (pairPreimage i)) at hc
    rw [hzq,(pair_preimage i).1] at hc
    have hzv : Commute z v := mul_inv_eq_iff_eq_mul.mp hc
    change v*z*v⁻¹ = z
    rw [hzv.symm.eq,mul_inv_cancel_right]
  have hhP : h ∈ localPairCentralizer := localPairCentralizer.mul_mem hg (pair_kernel_mem u hu)
  let w := v*h
  have hwP : w ∈ localPairCentralizer := localPairCentralizer.mul_mem (pair_kernel_mem v hv) hhP
  have hwz : (MulAut.conj w) z = z := by rw [show w = v*h from rfl,conjugate_mul,hfix,hvz]
  have hwt : (MulAut.conj w) t = t := by rw [show w = v*h from rfl,conjugate_mul]; exact hvs
  have hwC : (w : Model) ∈ centralizer (X : Set Model) := by
    rw [hgen,show nativePair ⊔ closure ({(z : Model),(t : Model)} : Set Model) =
      closure ((nativePair : Set Model) ∪ {(z : Model),(t : Model)}) from by
        rw [Subgroup.closure_union,Subgroup.closure_eq],centralizer_closure]
    rintro y (hy | hy)
    · have hwP' : (w : Model) ∈ centralizer (nativePair : Set Model) := by
        rw [centralizer_eq_local_map]
        exact mem_map_of_mem M.subtype hwP
      exact hwP' y hy
    · rcases hy with rfl | rfl
      · exact congrArg (fun v : M => (v : Model)) (mul_inv_eq_iff_eq_mul.mp hwz).symm
      · exact congrArg (fun v : M => (v : Model)) (mul_inv_eq_iff_eq_mul.mp hwt).symm
  refine ⟨w,hwC,?_⟩
  change starHom (v*h) = q
  rw [map_mul,MonoidHom.mem_ker.mp (starHom_ker.symm ▸ hv),hhq,one_mul]

/-- The full image is the literal exceptional order-sixteen container. -/
theorem exceptional_centralizer_image (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    ((centralizer (X : Set Model)).subgroupOf M).map starHom = imageBlock 0 := by
  apply Eq.symm
  apply eq_of_le_of_card_ge (exceptional_image_lifts X hpair hpure hpos hfour)
  rw [imageBlock_card]
  exact exceptional_centralizer_image_card_le X hpair hpure hpos hfour

/-- The entire ambient centralizer has order 256 for every actual pure
exceptional extension, independently of every choice of lift. -/
theorem exceptional_centralizer_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    Nat.card (centralizer (X : Set Model)) = 256 := by
  have hCM := (elementary_overgroup_placement X hpair).2
  let H := (centralizer (X : Set Model)).subgroupOf M
  let f := starHom.subgroupMap H
  have he : f.ker.map (M.subtype.comp H.subtype) = exceptionalSpace := by
    rw [show f.ker = max1Kernel.subgroupOf H from (ker_subgroupMap H starHom).trans
      (congrArg (fun K : Subgroup M => K.subgroupOf H) starHom_ker)]
    rw [← map_map,subgroupOf_map_subtype]
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,map_subgroupOf_eq_of_le hCM]
    exact (inf_comm _ _).trans (exceptional_centralizer_kernel_eq X hpair hpure hpos hfour)
  have hkcard : Nat.card f.ker = 16 := by
    rw [← card_map_of_injective (f := M.subtype.comp H.subtype)
      (M.subtype_injective.comp H.subtype_injective),he,exceptionalSpace_card]
  have hc := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top_of_surjective f (starHom.subgroupMap_surjective H),
    card_top,hkcard] at hc
  change 16 * Nat.card (H.map starHom) = Nat.card H at hc
  rw [show H.map starHom = imageBlock 0 from
    exceptional_centralizer_image X hpair hpure hpos hfour,imageBlock_card] at hc
  have hcard : Nat.card H = Nat.card (centralizer (X : Set Model)) :=
    Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv
  rw [hcard] at hc
  exact hc.symm

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
