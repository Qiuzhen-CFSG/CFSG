module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.DisplacementKernel
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.DisplacementActions


/-!
# Actual kernels and centralizers in the two pure image positions

Kernel displacement forces the image into two literal four-groups. Distinct
nonidentity elements in the exceptional position force the original kernel
to equal the native pair. Two lifts selected from the actual subgroup then
generate it together with that pair and determine its full ambient
centralizer. Its kernel section satisfies the two exact fixed-vector
equations. In the common position every kernel lies in one explicit set of
thirty-two coordinates, giving the corresponding order bound.

The final proper-extension application preserves purity, maximal TWO-local
status, and both full ambient conjugation transports. No chosen pair or lift
is asserted to be fixed by the whole normalizer. Identifying the full
centralizer and obtaining an intrinsic distinguished involution remain
separate geometric steps.
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

/-- In either certified position only three nonidentity image elements can
lift to a pure extension containing the native pair. -/
theorem pure_position_image_coordinates (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (r : Fin 2) (hpos : (X.subgroupOf M).map starHom ≤ imageBlock (r.castLE (by decide)))
    (p : StarGroup) (hp : p ∈ (X.subgroupOf M).map starHom) (hp1 : p ≠ 1) :
    ∃ j : Fin 3, p = element (pureIndex r j) := by
  obtain ⟨i,rfl⟩ := (mem_imageBlock_iff _ _).mp (hpos hp)
  have h0 := pure_extension_kernel_mask X hpair hpure _ hp hp1 ⟨818,by decide⟩
    (hpair (subset_closure (by simp)))
  have h1 := pure_extension_kernel_mask X hpair hpure _ hp hp1 ⟨1449,by decide⟩
    (hpair (subset_closure (by simp)))
  obtain ⟨j,hj⟩ := image_selection r i h0 h1
  exact ⟨j,congrArg element hj⟩

/-- The actual image lies in one of two explicit four-groups. -/
theorem pure_position_image_le (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (r : Fin 2) (hpos : (X.subgroupOf M).map starHom ≤ imageBlock (r.castLE (by decide))) :
    (X.subgroupOf M).map starHom ≤ pureBlock r := by
  intro p hp
  by_cases h1 : p = 1
  · exact h1 ▸ (pureBlock r).one_mem
  · obtain ⟨j,rfl⟩ := pure_position_image_coordinates X hpair hpure r hpos p hp h1
    exact pureIndex_mem r j

/-- An order-four actual image fills its explicit pure image container. -/
theorem pure_position_image_eq (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (r : Fin 2) (hpos : (X.subgroupOf M).map starHom ≤ imageBlock (r.castLE (by decide)))
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    (X.subgroupOf M).map starHom = pureBlock r := by
  apply eq_of_le_of_card_ge (pure_position_image_le X hpair hpure r hpos)
  rw [hfour,pureBlock_card]

/-- The actual kernel is contained in each of the displayed displacement
spaces, with no choice of lift added as a premise. -/
theorem pure_position_kernel_coordinates (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (r : Fin 2) (i : Fin 3)
    (hi : element (pureIndex r i) ∈ (X.subgroupOf M).map starHom)
    (m : Fin 2048) (hm : (kernelValue m.val : Model) ∈ X) :
    ∃ j : Fin 32, m.val = displacementMask r i j := by
  have hne : ∀ (r : Fin 2) (i : Fin 3), element (pureIndex r i) ≠ 1 := by
    intro r i he
    have he' := congrArg (fun p : StarGroup => p.val 0) he
    have hn : ∀ (r : Fin 2) (i : Fin 3), (element (pureIndex r i)).val 0 ≠ 0 := by decide +kernel
    exact hn r i he'
  obtain ⟨n,hn⟩ := pure_extension_kernel_mask X hpair hpure _ hi (hne r i) m hm
  obtain ⟨j,hj⟩ := displacement_coordinates r i n
  exact ⟨j,hn.symm.trans hj⟩

/-- Two distinct nonidentity elements in the exceptional image position
force the actual kernel to be exactly the original four-group. -/
theorem exceptional_kernel_eq_pair (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : element (pureIndex 0 i) ∈ (X.subgroupOf M).map starHom)
    (hj : element (pureIndex 0 j) ∈ (X.subgroupOf M).map starHom) :
    X ⊓ embeddedKernel = nativePair := by
  apply le_antisymm
  · intro w hw
    obtain ⟨u,hu,rfl⟩ := hw.2
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
    have he : kernelValue m.val = u := congrArg Subtype.val hm
    have hmem : (kernelValue m.val : Model) ∈ X := he.symm ▸ hw.1
    obtain ⟨k,hk⟩ := pure_position_kernel_coordinates X hpair hpure 0 i hi m hmem
    obtain ⟨l,hl⟩ := pure_position_kernel_coordinates X hpair hpure 0 j hj m hmem
    have hm' := exceptional_intersection i j k l hij (hk.symm.trans hl)
    rw [← hk] at hm'
    rw [← he]
    rcases hm' with h | h | h | h
    · rw [h,kernelValue_zero]; exact nativePair.one_mem
    · rw [h]; exact subset_closure (by simp)
    · rw [h]; exact subset_closure (by simp)
    · rw [h,show 1691 = Nat.xor 818 1449 from rfl,kernelValue_xor]
      exact nativePair.mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · refine le_inf hpair ?_
    apply (closure_le _).mpr
    rintro w (rfl | rfl) <;>
      exact mem_map_of_mem M.subtype (maskValue matrixA_mul_self matrixB_pow_four _).property

/-- The order-four exceptional position determines the original kernel
exactly; no second lift or kernel alternative is assumed. -/
theorem exceptional_four_kernel (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    X ⊓ embeddedKernel = nativePair := by
  have he := pure_position_image_eq X hpair hpure 0 hpos hfour
  exact exceptional_kernel_eq_pair X hpair hpure 0 1 (by decide)
    (he.symm ▸ pureIndex_mem 0 0) (he.symm ▸ pureIndex_mem 0 1)

/-- In the exceptional order-four position, two lifts selected from the
actual subgroup and the native pair generate the whole subgroup and determine
its full ambient centralizer. No selected lift is assumed invariant. -/
theorem exceptional_four_actual_lifts (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4) :
    ∃ z t : M, (z : Model) ∈ X ∧ (t : Model) ∈ X ∧
      starHom z = element 12 ∧ starHom t = element 64 ∧
      X = nativePair ⊔ closure ({(z : Model),(t : Model)} : Set Model) ∧
      centralizer (X : Set Model) = centralizer (nativePair : Set Model) ⊓
        centralizer ({(z : Model),(t : Model)} : Set Model) := by
  have himage := pure_position_image_eq X hpair hpure 0 hpos hfour
  have hk := exceptional_four_kernel X hpair hpure hpos hfour
  have hXM := (elementary_overgroup_placement X hpair).1
  obtain ⟨z,hz,hzq⟩ := himage.symm ▸ pureIndex_mem 0 0
  obtain ⟨t,ht,htq⟩ := himage.symm ▸ pureIndex_mem 0 1
  let A := nativePair ⊔ closure ({(z : Model),(t : Model)} : Set Model)
  have hzA : (z : Model) ∈ A := (show closure ({(z : Model),(t : Model)} : Set Model) ≤ A from le_sup_right) (subset_closure (by simp))
  have htA : (t : Model) ∈ A := (show closure ({(z : Model),(t : Model)} : Set Model) ≤ A from le_sup_right) (subset_closure (by simp))
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
  have hXA : X ≤ A := by
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
    have hmem := A.mul_mem ((show nativePair ≤ A from le_sup_left) hD) hu
    change ((w : Model) * (u : Model)⁻¹) * (u : Model) ∈ A at hmem
    simpa only [inv_mul_cancel_right] using hmem
  have hXAeq : X = A := le_antisymm hXA hAX
  refine ⟨z,t,hz,ht,hzq,htq,hXAeq,?_⟩
  have hAc : A = closure ((nativePair : Set Model) ∪ {(z : Model),(t : Model)}) := by
    rw [Subgroup.closure_union,Subgroup.closure_eq]
  rw [hXAeq,hAc,centralizer_closure]
  ext v
  simp only [mem_centralizer_iff,mem_inf,Set.mem_union,or_imp,forall_and]

private theorem kernel_commute_iff (z : M) (m : Fin 2048) :
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

/-- Exact kernel section of the full ambient centralizer in the exceptional
order-four case. The two equations are independent of the chosen actual lifts. -/
theorem exceptional_four_centralizer_kernel (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 0)
    (hfour : Nat.card ((X.subgroupOf M).map starHom) = 4)
    (m : Fin 2048) :
    (kernelValue m.val : Model) ∈ centralizer (X : Set Model) ↔
      SylowCore.starMask (element 12) m.val = m.val ∧
      SylowCore.starMask (element 64) m.val = m.val := by
  obtain ⟨z,t,hz,ht,hzq,htq,_,hC⟩ := exceptional_four_actual_lifts X hpair hpure hpos hfour
  rw [hC,mem_inf]
  have hp : (kernelValue m.val : Model) ∈ centralizer (nativePair : Set Model) := by
    rw [nativePair,centralizer_closure]
    rintro v (rfl | rfl) <;> exact congrArg (fun u : M => (u : Model)) (kernelValue_commute _ _).eq
  constructor
  · intro h
    have hz' : Commute z (kernelValue m.val) := Subtype.ext (h.2 _ (by simp))
    have ht' : Commute t (kernelValue m.val) := Subtype.ext (h.2 _ (by simp))
    exact ⟨hzq ▸ (kernel_commute_iff z m).mp hz', htq ▸ (kernel_commute_iff t m).mp ht'⟩
  · rintro ⟨hz',ht'⟩
    refine ⟨hp,?_⟩
    have hzc := (kernel_commute_iff z m).mpr (hzq.symm ▸ hz')
    have htc := (kernel_commute_iff t m).mpr (htq.symm ▸ ht')
    rintro v (rfl | rfl)
    · exact congrArg (fun u : M => (u : Model)) hzc.eq
    · exact congrArg (fun u : M => (u : Model)) htc.eq

/-- A nontrivial image in the common position puts every actual kernel
element in the same explicit thirty-two-element space. -/
theorem common_kernel_coordinates (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥)
    (m : Fin 2048) (hm : (kernelValue m.val : Model) ∈ X) :
    ∃ j : Fin 32, m.val = displacementMask 0 0 j := by
  obtain ⟨p,hp⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hp1 : p.val ≠ 1 := fun he => hp (Subtype.ext he)
  obtain ⟨i,hi⟩ := pure_position_image_coordinates X hpair hpure 1 hpos p.val p.property hp1
  have hmem : element (pureIndex 1 i) ∈ (X.subgroupOf M).map starHom := hi ▸ p.property
  obtain ⟨j,hj⟩ := pure_position_kernel_coordinates X hpair hpure 1 i hmem m hm
  exact ⟨j,by rw [common_displacement] at hj; exact hj⟩

/-- The common-position restriction bounds the original embedded kernel,
including every proper kernel possibility. -/
theorem common_kernel_card_le (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    Nat.card ↥(X ⊓ embeddedKernel) ≤ 32 := by
  classical
  have coords (v : ↥(X ⊓ embeddedKernel)) :
      ∃ j : Fin 32, (v : Model) = (kernelValue (displacementMask 0 0 j) : Model) := by
    obtain ⟨u,hu,huv⟩ := v.property.2
    change (u : Model) = (v : Model) at huv
    obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨u,hu⟩
    have he : kernelValue m.val = u := congrArg Subtype.val hm
    have hmem : (kernelValue m.val : Model) ∈ X := by rw [he,huv]; exact v.property.1
    obtain ⟨j,hj⟩ := common_kernel_coordinates X hpair hpure hpos hne m hmem
    refine ⟨j,?_⟩
    rw [← hj,he,huv]
  let f : ↥(X ⊓ embeddedKernel) → Fin 32 := fun v => Classical.choose (coords v)
  have hf (v : ↥(X ⊓ embeddedKernel)) :
      (v : Model) = (kernelValue (displacementMask 0 0 (f v)) : Model) := Classical.choose_spec (coords v)
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    rw [hf v,hf w,he]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hi

/-- The proper maximal pure-extension consumer now retains exact kernel
information in the two positions, alongside purity, maximality and both
whole ambient transports. -/
theorem maximal_pure_extension_kernel_positions (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hpair : nativePair ≤ X) (hlarge : 4 < Nat.card X)
    (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    ∃ (g : localPairCentralizer) (r : Fin 2),
      let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
      nativePair ≤ Y ∧ 4 < Nat.card Y ∧ Y ≤ M ∧
      centralizer (Y : Set Model) ≤ M ∧
      (∀ y ∈ Y, y ≠ 1 → IsConj a y) ∧
      IsMaximalTwoLocal (normalizer (Y : Set Model)) ∧
      (Y.subgroupOf M).map starHom ≤ pureBlock r ∧
      (Nat.card ((Y.subgroupOf M).map starHom) = 2 ∨
        (Y.subgroupOf M).map starHom = pureBlock r) ∧
      (r = 0 → Nat.card ((Y.subgroupOf M).map starHom) = 4 →
        Y ⊓ embeddedKernel = nativePair) ∧
      (r = 1 → ∀ m : Fin 2048, (kernelValue m.val : Model) ∈ Y →
        ∃ j : Fin 32, m.val = displacementMask 0 0 j) ∧
      centralizer (Y : Set Model) = (centralizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom ∧
      normalizer (Y : Set Model) = (normalizer (X : Set Model)).map
        (MulAut.conj (g.val : Model)).toMonoidHom := by
  obtain ⟨g,hP,hlargeY,hM,hC,hpY,hmY,hpos,hsize,hct,hnt⟩ :=
    maximal_pure_extension_two_positions X hpair hlarge hpure hmax
  let Y := X.map (MulAut.conj (g.val : Model)).toMonoidHom
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.map _
  have hn := maximal_pure_extension_image_ne_bot Y hP hpY hmY
  have choose (r : Fin 2)
      (hr : (Y.subgroupOf M).map starHom ≤ imageBlock (r.castLE (by decide))) :
      (Y.subgroupOf M).map starHom ≤ pureBlock r ∧
      (Nat.card ((Y.subgroupOf M).map starHom) = 2 ∨
        (Y.subgroupOf M).map starHom = pureBlock r) := by
    refine ⟨pure_position_image_le Y hP hpY r hr,?_⟩
    rcases hsize with h | h
    · exact Or.inl h
    · exact Or.inr (pure_position_image_eq Y hP hpY r hr h)
  rcases hpos with h0 | h1
  · exact ⟨g,0,hP,hlargeY,hM,hC,hpY,hmY,(choose 0 h0).1,(choose 0 h0).2,
      fun _ => exceptional_four_kernel Y hP hpY h0,
      fun he => (by cases he),hct,hnt⟩
  · exact ⟨g,1,hP,hlargeY,hM,hC,hpY,hmY,(choose 1 h1).1,(choose 1 h1).2,
      fun he => (by cases he),fun _ => common_kernel_coordinates Y hP hpY h1 hn,hct,hnt⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
