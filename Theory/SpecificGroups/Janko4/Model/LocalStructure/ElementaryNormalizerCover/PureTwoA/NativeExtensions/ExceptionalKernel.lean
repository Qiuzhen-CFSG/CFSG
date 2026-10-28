module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.ExceptionalTransitivity
import Mathlib.Tactic.Group

/-!
# Exact kernel section and upper bound for exceptional centralizers

The two exceptional image generators fix one explicit elementary subgroup
of order sixteen in the original binary kernel. This is the exact kernel
section of the full ambient centralizer for every actual pure extension.
The pointwise image centralizer has order sixteen, giving a full centralizer
upper bound of 256 without a preferred lift or an assumed row marking.
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



@[expose] def exceptionalMask : Fin 16 → ℕ :=
  ![0,7,320,327,626,629,818,821,1257,1262,1449,1454,1691,1692,2011,2012]
private theorem mask_bound : ∀ j : Fin 16, exceptionalMask j < 2048 := by decide +kernel
private theorem mask_xor : ∀ i j : Fin 16,
    exceptionalMask i ^^^ exceptionalMask j =
      exceptionalMask ⟨i.val ^^^ j.val,Nat.xor_lt_two_pow (n := 4) i.isLt j.isLt⟩ := by decide +kernel

/-- The literal fixed subgroup in the original binary kernel. -/
@[expose] def exceptionalKernel : Subgroup M where
  carrier := {u | ∃ j : Fin 16, u = kernelValue (exceptionalMask j)}
  one_mem' := ⟨0,kernelValue_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨⟨i.val ^^^ j.val,Nat.xor_lt_two_pow (n := 4) i.isLt j.isLt⟩,by
      rw [← kernelValue_xor]
      exact congrArg kernelValue (by simpa only [Nat.xor_eq] using mask_xor i j)⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨i,inv_eq_of_mul_eq_one_left (kernelValue_square _)⟩

@[expose] def exceptionalSpace : Subgroup Model := exceptionalKernel.map M.subtype

theorem exceptionalKernel_le : exceptionalKernel ≤ max1Kernel := by
  rintro _ ⟨i,rfl⟩
  exact (maskValue matrixA_mul_self matrixB_pow_four _).property

theorem exceptionalSpace_le_kernel : exceptionalSpace ≤ embeddedKernel := map_mono exceptionalKernel_le

theorem mem_exceptionalSpace (v : Model) : v ∈ exceptionalSpace ↔
    ∃ i : Fin 16, v = (kernelValue (exceptionalMask i) : Model) := by
  constructor
  · rintro ⟨u,⟨i,rfl⟩,rfl⟩; exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩; exact mem_map_of_mem M.subtype (show _ ∈ exceptionalKernel from ⟨i,rfl⟩)

theorem exceptionalSpace_card : Nat.card exceptionalSpace = 16 := by
  let f : Fin 16 → exceptionalKernel := fun j => ⟨kernelValue (exceptionalMask j),j,rfl⟩
  have hj : Function.Injective exceptionalMask := by decide +kernel
  have hi : Function.Injective f := by
    intro i j h
    exact hj (kernelValue_injective (mask_bound i) (mask_bound j)
      (congrArg (fun u : exceptionalKernel => (u : M)) h))
  have hs : Function.Surjective f := by
    rintro ⟨u,i,rfl⟩; exact ⟨i,rfl⟩
  rw [exceptionalSpace,card_map_of_injective M.subtype_injective,
    ← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_fin]

private def actionRows : Fin 2 → Fin 11 → ℕ :=
  ![![2,1,4,1467,1440,1418,256,946,64,857,1640],
    ![1128,1881,822,503,47,480,71,128,263,1187,81]]
private theorem action_eq (i : Fin 2) (m : ℕ) :
    SylowCore.starMask (element (pureIndex 0 i.castSucc)) m = maskImage (actionRows i) m := by
  have hr : ∀ (i : Fin 2) (j : Fin 11), actionRows i j =
      pairLabel ((element (pureIndex 0 i.castSucc)).val (basisPair j).1)
        ((element (pureIndex 0 i.castSucc)).val (basisPair j).2) := by decide +kernel
  unfold SylowCore.starMask
  congr 1
  exact (funext (hr i)).symm
private def fixedCode (m : ℕ) : Fin 16 :=
  ⟨(m / 4) % 2 + 2 * ((m / 256) % 2) + 4 * ((m / 512) % 2) + 8 * ((m / 1024) % 2),by omega⟩
private theorem fixed_only : ∀ m : Fin 2048,
    maskImage (actionRows 0) m.val = m.val → maskImage (actionRows 1) m.val = m.val →
      exceptionalMask (fixedCode m.val) = m.val := by decide +kernel
private theorem mask_fixed : ∀ i : Fin 16,
    maskImage (actionRows 0) (exceptionalMask i) = exceptionalMask i ∧
    maskImage (actionRows 1) (exceptionalMask i) = exceptionalMask i := by decide +kernel
private theorem fixed_iff (m : Fin 2048) :
    (SylowCore.starMask (element 12) m.val = m.val ∧
      SylowCore.starMask (element 64) m.val = m.val) ↔
      ∃ i : Fin 16, m.val = exceptionalMask i := by
  rw [show element 12 = element (pureIndex 0 (0 : Fin 2).castSucc) from rfl,
    show element 64 = element (pureIndex 0 (1 : Fin 2).castSucc) from rfl,
    action_eq,action_eq]
  constructor
  · rintro ⟨h0,h1⟩
    exact ⟨fixedCode m.val,(fixed_only m h0 h1).symm⟩
  · rintro ⟨i,hi⟩
    rw [hi]
    exact mask_fixed i

/-- Exact kernel intersection of the entire ambient centralizer, for every
actual lift configuration in the exceptional branch. -/
theorem exceptional_centralizer_kernel_eq (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    centralizer (X : Set Model) ⊓ embeddedKernel = exceptionalSpace := by
  apply le_antisymm
  · rintro v ⟨hv,u,hu,rfl⟩
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
    have he : kernelValue m.val = u := congrArg Subtype.val hm
    have hf := (exceptional_four_centralizer_kernel X hpair hpure hpos hfour m).mp
      (he.symm ▸ hv)
    obtain ⟨i,hi⟩ := (fixed_iff m).mp hf
    exact (mem_exceptionalSpace _).mpr ⟨i,congrArg (fun u : M => (u : Model))
      (he.symm.trans (congrArg kernelValue hi))⟩
  · intro v hv
    refine ⟨?_,exceptionalSpace_le_kernel hv⟩
    obtain ⟨i,rfl⟩ := (mem_exceptionalSpace _).mp hv
    apply (exceptional_four_centralizer_kernel X hpair hpure hpos hfour
      ⟨exceptionalMask i,mask_bound i⟩).mpr
    exact (fixed_iff _).mpr ⟨i,rfl⟩

private def centralIndex : Fin 16 → Fin 96 :=
  ![0,9,12,19,29,32,41,46,49,56,64,69,73,78,88,95]
private theorem central_image_only (i : Fin 96)
    (h0 : Commute (element i) (element 12)) (h1 : Commute (element i) (element 64)) :
    ∃ j : Fin 16, i = centralIndex j := by
  have hp0 := congrArg Subtype.val h0.eq
  have hp1 := congrArg Subtype.val h1.eq
  have hs : ∀ i : Fin 96,
      (element i).val * (element 12).val = (element 12).val * (element i).val →
      (element i).val * (element 64).val = (element 64).val * (element i).val →
      ∃ j : Fin 16, i = centralIndex j := by decide +kernel
  exact hs i hp0 hp1

/-- The literal image of the full centralizer has at most sixteen elements. -/
theorem exceptional_centralizer_image_card_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    Nat.card (((centralizer (X : Set Model)).subgroupOf M).map starHom) ≤ 16 := by
  classical
  let A := ((centralizer (X : Set Model)).subgroupOf M).map starHom
  have himage := pure_position_image_eq X hpair hpure 0 hpos hfour
  have coords (p : A) : ∃ j : Fin 16, p.val = element (centralIndex j) := by
    obtain ⟨z,hz,hzq⟩ := p.property
    have hzP := (centralizer_le hpair) hz
    rw [centralizer_eq_local_map] at hzP
    obtain ⟨w,hw,hwz⟩ := hzP
    have hwz' : w = z := Subtype.ext hwz
    have hzlocal : z ∈ localPairCentralizer := hwz' ▸ hw
    obtain ⟨i,hi⟩ := (mem_pair_image_iff _).mp (mem_map_of_mem starHom hzlocal)
    have hc (j : Fin 3) : Commute (element i) (element (pureIndex 0 j)) := by
      obtain ⟨v,hv,hvq⟩ := himage.symm ▸ pureIndex_mem 0 j
      have hh : Commute z v := (show Commute v z from Subtype.ext (hz _ hv)).symm
      exact hi.symm ▸ hvq ▸ hh.map starHom
    obtain ⟨j,rfl⟩ := central_image_only i (hc 0) (hc 1)
    exact ⟨j,(hi.trans hzq).symm⟩
  let f : A → Fin 16 := fun p => Classical.choose (coords p)
  have hf (p : A) : p.val = element (centralIndex (f p)) := Classical.choose_spec (coords p)
  have hi : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    rw [hf p,hf q,he]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

/-- An upper bound for the entire ambient centralizer. Its equality and
native conjugacy class require the remaining actual lift calculation. -/
theorem exceptional_centralizer_card_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    Nat.card (centralizer (X : Set Model)) ≤ 256 := by
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
  have hcard : Nat.card H = Nat.card (centralizer (X : Set Model)) :=
    Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv
  rw [hcard] at hc
  have hb := exceptional_centralizer_image_card_le X hpair hpure hpos hfour
  change Nat.card (H.map starHom) ≤ 16 at hb
  omega

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
