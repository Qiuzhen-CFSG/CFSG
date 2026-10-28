module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalApplication
import Mathlib.Tactic.Group

/-!
# Strict two-local enlargement in the exceptional image position

The literal kernel element of mask 64 normalizes the full centralizer of
EVERY exceptional pure extension: its displacement on the whole centralizer
image lies in the exact sixteen-element kernel section. Its displacement on
an actual lift of image 12 is mask 320, outside the original subgroup's exact
kernel (the native pair). It therefore fails to normalize the original group.
The full centralizer has order 256, so its normalizer is two-local. This gives
a strict two-local enlargement and excludes the exceptional position under
the original maximal-two-local hypothesis, without needing ambient fusion of
the centralizer to a separately marked native eight.
Source: Kleidman--Wilson (1988), Section 2.1, p.489; specialized maximal-two-local
route through the actual centralizer and its proved kernel/image identities.
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

private theorem kernel64_displacement (z : M) :
    (MulAut.conj (kernelValue 64)) z * z⁻¹ =
      kernelValue (64 ^^^ SylowCore.starMask (starHom z) 64) := by
  have hc := kernel_conjugation z 64
  change z * kernelValue 64 * z⁻¹ = kernelValue (SylowCore.starMask (starHom z) 64) at hc
  have hx : kernelValue (64 ^^^ SylowCore.starMask (starHom z) 64) =
      kernelValue 64 * kernelValue (SylowCore.starMask (starHom z) 64) := by
    simpa only [Nat.xor_eq] using kernelValue_xor 64 (SylowCore.starMask (starHom z) 64)
  rw [hx,← hc]
  simp only [MulAut.conj_apply,inv_eq_of_mul_eq_one_left (kernelValue_square 64),mul_assoc]

private theorem block_displacement (q : StarGroup) (hq : q ∈ imageBlock 0) :
    kernelValue (64 ^^^ SylowCore.starMask q 64) ∈ exceptionalKernel := by
  obtain ⟨i,rfl⟩ := (mem_imageBlock_iff _ _).mp hq
  have hh : ∀ i : Fin 16, ∃ j : Fin 16,
      64 ^^^ SylowCore.starMask (element (blockIndex 0 i)) 64 = exceptionalMask j := by
    decide +kernel
  obtain ⟨j,hj⟩ := hh i
  exact ⟨j,congrArg kernelValue hj⟩

private theorem mask320_not_pair : (kernelValue 320 : Model) ∉ nativePair := by
  intro hm
  have hsq (m : ℕ) : (kernelValue m : Model) * kernelValue m = 1 :=
    congrArg (fun z : M => (z : Model)) (kernelValue_square m)
  have hh := (mem_closure_pair_iff (kernelValue 818 : Model) (kernelValue 1449)
    (hsq 818) (hsq 1449) ((kernelValue_commute _ _).map M.subtype) _).mp hm
  have hn (m : ℕ) (hb : m < 2048) (hne : 320 ≠ m)
      (he : (kernelValue 320 : Model) = kernelValue m) : False :=
    hne (kernelValue_injective (by decide) hb (Subtype.ext he))
  rcases hh with h | h | h | h
  · exact hn 0 (by decide) (by decide) (h.trans (congrArg (fun z : M => (z : Model)) kernelValue_zero.symm))
  · exact hn 818 (by decide) (by decide) h
  · exact hn 1449 (by decide) (by decide) h
  · exact hn 1691 (by decide) (by decide) (h.trans
      (congrArg (fun z : M => (z : Model)) (kernelValue_xor 818 1449).symm))

/-- The same literal kernel actor normalizes the ENTIRE actual centralizer,
independently of the selected lifts in the exceptional extension. -/
theorem exceptional_kernel64_normalizes_centralizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    (kernelValue 64 : Model) ∈ normalizer (centralizer (X : Set Model) : Set Model) := by
  let C := centralizer (X : Set Model)
  have hCM : C ≤ M := (elementary_overgroup_placement X hpair).2
  have hD : exceptionalSpace ≤ C := by
    rw [← exceptional_centralizer_kernel_eq X hpair hpure hpos hfour]
    exact inf_le_left
  have hmap : C.map (MulAut.conj (kernelValue 64 : Model)).toMonoidHom ≤ C := by
    rintro _ ⟨c,hc,rfl⟩
    let z : M := ⟨c,hCM hc⟩
    have hq : starHom z ∈ imageBlock 0 := by
      rw [← exceptional_centralizer_image X hpair hpure hpos hfour]
      exact mem_map_of_mem starHom (show z ∈ C.subgroupOf M from hc)
    have hd : (kernelValue (64 ^^^ SylowCore.starMask (starHom z) 64) : Model) ∈ C :=
      hD (mem_map_of_mem M.subtype (block_displacement _ hq))
    have he := congrArg (fun w : M => (w : Model)) (kernel64_displacement z)
    have hh := C.mul_mem (he.symm ▸ hd) hc
    change (MulAut.conj (kernelValue 64 : Model)) c * c⁻¹ * c ∈ C at hh
    change (MulAut.conj (kernelValue 64 : Model)) c ∈ C
    simpa only [inv_mul_cancel_right] using hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge hmap
  rw [card_map_of_injective (MulAut.conj (kernelValue 64 : Model)).injective]

/-- The original subgroup is moved: its actual image-12 lift acquires mask
320, which is excluded by its exact native-pair kernel. -/
theorem exceptional_kernel64_not_normalizer (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    (kernelValue 64 : Model) ∉ normalizer (X : Set Model) := by
  intro hn
  obtain ⟨z,_,hz,_,hzq,_,_,_⟩ := exceptional_four_actual_lifts X hpair hpure hpos hfour
  have hgz : (MulAut.conj (kernelValue 64 : Model)) (z : Model) ∈ X := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hn]
    exact mem_map_of_mem _ hz
  have hd := X.mul_mem hgz (X.inv_mem hz)
  have he := kernel64_displacement z
  rw [hzq,show 64 ^^^ SylowCore.starMask (element 12) 64 = 320 from by decide +kernel] at he
  have hm : (kernelValue 320 : Model) ∈ X :=
    (congrArg (fun w : M => (w : Model)) he) ▸ hd
  apply mask320_not_pair
  rw [← exceptional_four_kernel X hpair hpure hpos hfour]
  exact ⟨hm,mem_map_of_mem M.subtype (maskValue _ _ _).property⟩

/-- A genuine strict enlargement to another two-local, using the full
centralizer's proved order 256 rather than an assumed elementary marking. -/
theorem exceptional_strict_twoLocal_enlargement (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    IsTwoLocal (normalizer (centralizer (X : Set Model) : Set Model)) ∧
      normalizer (X : Set Model) < normalizer (centralizer (X : Set Model) : Set Model) := by
  have hc := exceptional_centralizer_card X hpair hpure hpos hfour
  have hne : centralizer (X : Set Model) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hc
    contradiction
  refine ⟨⟨_,hne,IsPGroup.of_card (p := 2) (n := 8) hc,rfl⟩,?_⟩
  apply lt_of_le_of_ne (normalizer_le_normalizer_centralizer X)
  intro he
  exact exceptional_kernel64_not_normalizer X hpair hpure hpos hfour
    (he.symm ▸ exceptional_kernel64_normalizes_centralizer X hpair hpure hpos hfour)

/-- The exceptional position is impossible at maximal TWO-local level. -/
theorem exceptional_not_maximal (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    ¬ IsMaximalTwoLocal (normalizer (X : Set Model)) := by
  intro hm
  obtain ⟨hl,hs⟩ := exceptional_strict_twoLocal_enlargement X hpair hpure hpos hfour
  exact hs.ne (hm.eq_of_le hl hs.le)

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
