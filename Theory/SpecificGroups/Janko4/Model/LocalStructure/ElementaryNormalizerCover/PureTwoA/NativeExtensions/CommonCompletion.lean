module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonSpace
public import Theory.ElementaryAbelian.Join
import Mathlib.Tactic.Group

/-!
# Pure completion of an actual common-image extension

For an elementary pure extension whose literal Mathieu image is the common
four-group, adjoining its 32-element common displacement space gives a pure
self-centralizing subgroup of order 128. The proof uses all actual lifts:
each common-kernel translate of a nontrivial lift is kernel-conjugate to it.
The stabilizer and fixed-kernel certificates then determine the full ambient
centralizer of the completion.

Consequently the actual double centralizer is elementary and pure. It
contains the original subgroup and lies in the completion; maximal
TWO-locality identifies its whole normalizer with the original one. This
intrinsic replacement does not assert that the original normalizer preserves
the binary kernel or a chosen lift. The distinguishing rank geometry and
final local placement remain separate obligations.
Source: Kleidman--Wilson (1988), Section 2.1, p.489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion Simplicity.Max1Fusion.KernelOrbits
open NativePair NativePair.Stabilizer LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction DisplacementActions
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup
  Cardinality.localKernel basis
set_option backward.isDefEq.respectTransparency true

private theorem commonSpace_elementary : IsElementaryAbelian 2 commonSpace := by
  let : IsElementaryAbelian 2 max1Kernel := localKernel_elementary _ _
  let : IsElementaryAbelian 2 commonKernel := IsElementaryAbelian.of_le commonKernel_le
  exact IsElementaryAbelian.map M.subtype

private theorem common_block_le : pureBlock 1 ≤ imageBlock 1 := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  apply (mem_imageBlock_iff _ _).mpr
  fin_cases i
  · exact ⟨4,rfl⟩
  · exact ⟨11,rfl⟩

theorem commonSpace_le_centralizer (X : Subgroup Model) (hXM : X ≤ M)
    (himage : (X.subgroupOf M).map starHom ≤ pureBlock 1) :
    commonSpace ≤ centralizer (X : Set Model) := by
  intro d hd x hx
  let u : M := ⟨x,hXM hx⟩
  have hu : starHom u ∈ pureBlock 1 := himage (mem_map_of_mem starHom hx)
  exact (commonSpace_centralized u hu d hd).symm

/-- Adjoin the entire forced common displacement space to the actual subgroup. -/
@[expose] def commonCompletion (X : Subgroup Model) : Subgroup Model := X ⊔ commonSpace

theorem commonCompletion_elementary (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXM : X ≤ M) (himage : (X.subgroupOf M).map starHom ≤ pureBlock 1) :
    IsElementaryAbelian 2 (commonCompletion X) := by
  let := commonSpace_elementary
  exact IsElementaryAbelian.sup_of_le_centralizer (commonSpace_le_centralizer X hXM himage)

private theorem common_product_conjugate (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom ≤ pureBlock 1)
    (z : M) (hz : (z : Model) ∈ X) (hk : z ∉ max1Kernel)
    (d : M) (hd : d ∈ commonKernel) : IsConj (z : Model) ((z * d : M) : Model) := by
  have hp1 : starHom z ≠ 1 := by
    intro he; exact hk (starHom_ker ▸ MonoidHom.mem_ker.mpr he)
  obtain ⟨i,hi⟩ := pure_position_image_coordinates X hpair hpure 1
    (himage.trans common_block_le) (starHom z) (mem_map_of_mem starHom hz) hp1
  obtain ⟨n,hn⟩ := commonSpace_displacement i d hd
  have hz2 : z * z = 1 := by
    apply Subtype.ext
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : Model) hz
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz2
  have hni : (kernelValue n.val)⁻¹ = kernelValue n.val :=
    inv_eq_of_mul_eq_one_left (kernelValue_square _)
  have hc := kernel_conjugation z n.val
  have hd' : d = z⁻¹ * kernelValue n.val * z * (kernelValue n.val)⁻¹ := by
    have hx (r s : ℕ) : kernelValue (r ^^^ s) = kernelValue r * kernelValue s := by
      simpa only [Nat.xor_eq] using kernelValue_xor r s
    change z * kernelValue n.val * z⁻¹ = kernelValue (SylowCore.starMask (starHom z) n.val) at hc
    rw [hn,hx,← hi,← hc,hzi,hni]
  refine isConj_iff.mpr ⟨(kernelValue n.val : Model),?_⟩
  change ((kernelValue n.val * z * (kernelValue n.val)⁻¹ : M) : Model) = _
  apply congrArg (fun u : M => (u : Model))
  rw [hd']
  group

/-- Purity holds on every actual lift and every permitted common-kernel
extension, without choosing a preferred lift. -/
theorem commonCompletion_pure (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom ≤ pureBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    ∀ v ∈ commonCompletion X, v ≠ 1 → IsConj a v := by
  have hXM := (elementary_overgroup_placement X hpair).1
  have hc := commonSpace_le_centralizer X hXM himage
  intro v hv hv1
  have hv' : v ∈ (X : Set Model) * (commonSpace : Set Model) := by
    rw [← coe_mul_of_right_le_normalizer_left X commonSpace
      (hc.trans (centralizer_le_normalizer _))]
    exact hv
  obtain ⟨x,hx,d,hd,rfl⟩ := hv'
  let z : M := ⟨x,hXM hx⟩
  obtain ⟨u,hu,rfl⟩ := hd
  by_cases hk : z ∈ max1Kernel
  · have hxD : x ∈ commonSpace := by
      obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨z,hk⟩
      have he : kernelValue m.val = z := congrArg Subtype.val hm
      have hmem : (kernelValue m.val : Model) ∈ X := he.symm ▸ hx
      obtain ⟨j,hj⟩ := common_kernel_coordinates X hpair hpure
        (himage.trans common_block_le) hne m hmem
      apply (mem_commonSpace _).mpr
      exact ⟨j,congrArg (fun u : M => (u : Model)) (he.symm.trans (congrArg kernelValue hj))⟩
    exact commonSpace_pure _ (commonSpace.mul_mem hxD (mem_map_of_mem M.subtype hu)) hv1
  · have hx1 : x ≠ 1 := by
      intro he
      exact hk ((Subtype.ext he : z = 1).symm ▸ max1Kernel.one_mem)
    exact (hpure x hx hx1).trans (common_product_conjugate X hpair hpure himage z hx hk u hu)

/-- For full common four-image, the completion is its full ambient
centralizer. This uses both actual lifts through their original projection. -/
theorem commonCompletion_self_centralizing (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1) :
    centralizer (commonCompletion X : Set Model) = commonCompletion X := by
  have hXM := (elementary_overgroup_placement X hpair).1
  let := commonCompletion_elementary X hXM himage.le
  apply le_antisymm
  · intro v hv
    have hvC : v ∈ centralizer (X : Set Model) := (centralizer_le (show X ≤ commonCompletion X from le_sup_left)) hv
    have hvM := (elementary_overgroup_placement X hpair).2 hvC
    let z : M := ⟨v,hvM⟩
    have hq : starHom z ∈ pureBlock 1 := commonSpace_centralizer_image z
      ((centralizer_le hpair) hvC) ((centralizer_le (show commonSpace ≤ commonCompletion X from le_sup_right)) hv)
    obtain ⟨x,hx,hxq⟩ := himage.symm ▸ hq
    have hk : z * x⁻¹ ∈ max1Kernel := by
      rw [← starHom_ker]
      apply MonoidHom.mem_ker.mpr
      rw [map_mul,map_inv,hxq,mul_inv_cancel]
    have hd : ((z * x⁻¹ : M) : Model) ∈ commonSpace := by
      rw [← common_centralizer_kernel X hXM himage]
      exact ⟨(centralizer (X : Set Model)).mul_mem hvC
        ((centralizer (X : Set Model)).inv_mem (X.le_centralizer hx)),
        mem_map_of_mem M.subtype hk⟩
    have hmem := (commonCompletion X).mul_mem (mem_sup_right hd) (mem_sup_left hx)
    change ((z : Model) * (x : Model)⁻¹) * (x : Model) ∈ commonCompletion X at hmem
    simpa only [inv_mul_cancel_right] using hmem
  · exact (commonCompletion X).le_centralizer


/-- The completion retains exactly the common kernel. -/
theorem commonCompletion_kernel (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1) :
    commonCompletion X ⊓ embeddedKernel = commonSpace := by
  have hXM := (elementary_overgroup_placement X hpair).1
  have hH : commonCompletion X ≤ centralizer (X : Set Model) :=
    sup_le X.le_centralizer (commonSpace_le_centralizer X hXM himage.le)
  apply le_antisymm
  · rw [← common_centralizer_kernel X hXM himage]
    exact inf_le_inf_right _ hH
  · exact le_inf le_sup_right commonSpace_le_kernel

/-- Its quotient is the same literal common four-image. -/
theorem commonCompletion_image (X : Subgroup Model) (hXM : X ≤ M) :
    ((commonCompletion X).subgroupOf M).map starHom = (X.subgroupOf M).map starHom := by
  have hDM : commonSpace ≤ M := commonSpace_le_kernel.trans (map_subtype_le _)
  have hD : commonSpace.subgroupOf M = commonKernel :=
    comap_map_eq_self_of_injective M.subtype_injective commonKernel
  have hDb : commonKernel.map starHom = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,starHom_ker]
    exact commonKernel_le
  rw [commonCompletion,subgroupOf_sup hXM hDM,Subgroup.map_sup,hD,hDb,sup_bot_eq]

/-- The full common-image completion has order 128. -/
theorem commonCompletion_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1) :
    Nat.card (commonCompletion X) = 128 := by
  have hXM := (elementary_overgroup_placement X hpair).1
  have hHM : commonCompletion X ≤ M :=
    sup_le hXM (commonSpace_le_kernel.trans (map_subtype_le _))
  let H := (commonCompletion X).subgroupOf M
  let f := starHom.subgroupMap H
  have he : f.ker.map (M.subtype.comp H.subtype) = commonSpace := by
    rw [show f.ker = max1Kernel.subgroupOf H from (ker_subgroupMap H starHom).trans
      (congrArg (fun K : Subgroup M => K.subgroupOf H) starHom_ker)]
    rw [← map_map,subgroupOf_map_subtype]
    rw [Subgroup.map_inf _ _ _ M.subtype_injective,map_subgroupOf_eq_of_le hHM]
    exact (inf_comm _ _).trans (commonCompletion_kernel X hpair himage)
  have hkcard : Nat.card f.ker = 32 := by
    have hfI : Function.Injective (M.subtype.comp H.subtype) := M.subtype_injective.comp H.subtype_injective
    rw [← card_map_of_injective (f := M.subtype.comp H.subtype) hfI,he,commonSpace_card]
  have hc := f.ker.card_mul_index
  have hf : Function.Surjective f := starHom.subgroupMap_surjective H
  rw [index_ker,MonoidHom.range_eq_top_of_surjective f hf,card_top,hkcard] at hc
  have hi : Nat.card (H.map starHom) = 4 := by
    rw [show H.map starHom = pureBlock 1 from (commonCompletion_image X hXM).trans himage,pureBlock_card]
  rw [hi] at hc
  have hcard : Nat.card H = Nat.card (commonCompletion X) :=
    Nat.card_congr (subgroupOfEquivOfLe hHM).toEquiv
  rw [hcard] at hc
  exact hc.symm

/-- The intrinsic double centralizer of the actual subgroup lies in its
pure self-centralizing completion. It contains the original subgroup. -/
theorem common_double_centralizer_bounds (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1) :
    X ≤ centralizer (centralizer (X : Set Model) : Set Model) ∧
    centralizer (centralizer (X : Set Model) : Set Model) ≤ commonCompletion X := by
  refine ⟨?_,?_⟩
  · simpa only [closure_eq] using closure_le_centralizer_centralizer (X : Set Model)
  · have hH : commonCompletion X ≤ centralizer (X : Set Model) :=
      sup_le X.le_centralizer (commonSpace_le_centralizer X
        (elementary_overgroup_placement X hpair).1 himage.le)
    have h := centralizer_le hH
    rwa [commonCompletion_self_centralizing X hpair himage] at h

/-- A characteristic pure enlargement for the whole original normalizer.
At maximal TWO-local level its normalizer equals the original normalizer. -/
theorem common_double_centralizer_maximal (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1)
    (hmax : IsMaximalTwoLocal (normalizer (X : Set Model))) :
    let Z := centralizer (centralizer (X : Set Model) : Set Model)
    X ≤ Z ∧ IsElementaryAbelian 2 Z ∧
      (∀ z ∈ Z, z ≠ 1 → IsConj a z) ∧
      normalizer (Z : Set Model) = normalizer (X : Set Model) := by
  dsimp only
  let Z := centralizer (centralizer (X : Set Model) : Set Model)
  have hb := common_double_centralizer_bounds X hpair himage
  let := commonCompletion_elementary X (elementary_overgroup_placement X hpair).1 himage.le
  let he : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le hb.2
  have hn : (X.subgroupOf M).map starHom ≠ ⊥ :=
    maximal_pure_extension_image_ne_bot X hpair hpure hmax
  have hpZ := fun z hz hz1 => commonCompletion_pure X hpair hpure himage.le hn z (hb.2 hz) hz1
  have hZne : Z ≠ ⊥ := by
    intro h
    have hP : nativePair ≤ ⊥ := h ▸ (hpair.trans hb.1)
    have hcard := nativePair_card
    rw [le_bot_iff.mp hP,card_bot] at hcard
    contradiction
  have hl : IsTwoLocal (normalizer (Z : Set Model)) :=
    ⟨Z,hZne,IsElementaryAbelian.isPGroup 2 Z,rfl⟩
  have hnZ : normalizer (X : Set Model) ≤ normalizer (Z : Set Model) :=
    (normalizer_le_normalizer_centralizer X).trans
      (normalizer_le_normalizer_centralizer (centralizer (X : Set Model)))
  exact ⟨hb.1,he,hpZ,(hmax.eq_of_le hl hnZ).symm⟩

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
