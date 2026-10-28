module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonLiftProduct
public import Theory.ElementaryAbelian.AbelianNormalClosure
import Mathlib.Tactic.Group

/-!
# The fixed common group and all its actual subextensions

The native common group is elementary, pure, and self-centralizing of
order 128. The checked lift product supplies the fourth quotient fiber;
kernel displacement supplies purity throughout every fiber. Every pure
native-pair extension with nontrivial common image lies in this same group.
Its full double centralizer therefore lies there too, without assuming
that its normalizer preserves a selected lift or the original kernel.
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
  Cardinality.localKernel basis localX localY
set_option backward.isDefEq.respectTransparency true

private def liftGroup : Subgroup M := closure (Set.range commonLift)
private theorem lift_square (i : Fin 2) : commonLift i * commonLift i = 1 := by
  change (MulAut.conj _) _ * (MulAut.conj _) _ = _
  rw [← map_mul,localX_mul_self,map_one]
private theorem lift_commute (i j : Fin 2) : Commute (commonLift i) (commonLift j) := by
  fin_cases i <;> fin_cases j
  · exact Commute.refl _
  · exact commonLift_commute
  · exact commonLift_commute.symm
  · exact Commute.refl _
private theorem lift_elementary : IsElementaryAbelian 2 liftGroup := by
  let : IsMulCommutative (closure (Set.range commonLift)) := isMulCommutative_closure (by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact lift_commute i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro _ ⟨i,rfl⟩
  simpa only [pow_two] using lift_square i
private theorem lift_coordinates (z : M) (hz : z ∈ liftGroup) :
    z = 1 ∨ z = commonLift 0 ∨ z = commonLift 1 ∨ z = commonLift 0 * commonLift 1 := by
  obtain ⟨v,rfl⟩ := (mem_closure_iff_binaryProduct commonLift lift_square lift_commute z).mp hz
  have h : ∀ v : Fin 2 → Bool,
      binaryProduct commonLift v = 1 ∨ binaryProduct commonLift v = commonLift 0 ∨
      binaryProduct commonLift v = commonLift 1 ∨
      binaryProduct commonLift v = commonLift 0 * commonLift 1 := by
    intro v
    have hv : v = ![v 0,v 1] := by funext i; fin_cases i <;> rfl
    rw [hv]
    cases h0 : v 0 <;> cases h1 : v 1 <;> simp [binaryProduct]
  exact h v

private theorem lift_image : liftGroup.map starHom = pureBlock 1 := by
  rw [liftGroup,MonoidHom.map_closure,← Set.range_comp]
  have he : starHom ∘ commonLift = fun i : Fin 2 => element (pureIndex 1 i.castSucc) :=
    funext commonLift_projection
  rw [he]
  rfl

private theorem common_model_map : commonModel = (commonKernel ⊔ liftGroup).map M.subtype := by
  rw [Subgroup.map_sup,liftGroup,MonoidHom.map_closure,← Set.range_comp]
  rfl

theorem commonModel_le_max1 : commonModel ≤ M := by
  rw [common_model_map]
  exact map_subtype_le _

theorem commonModel_image : (commonModel.subgroupOf M).map starHom = pureBlock 1 := by
  rw [common_model_map,show ((commonKernel ⊔ liftGroup).map M.subtype).subgroupOf M =
    commonKernel ⊔ liftGroup from comap_map_eq_self_of_injective M.subtype_injective _]
  have hD : commonKernel.map starHom = ⊥ := by
    rw [Subgroup.map_eq_bot_iff,starHom_ker]
    exact commonKernel_le
  rw [Subgroup.map_sup,hD,bot_sup_eq,lift_image]

theorem commonModel_elementary : IsElementaryAbelian 2 commonModel := by
  let : IsElementaryAbelian 2 max1Kernel := localKernel_elementary _ _
  let : IsElementaryAbelian 2 commonKernel := IsElementaryAbelian.of_le commonKernel_le
  let := lift_elementary
  have hc : liftGroup ≤ centralizer (commonKernel : Set M) := by
    intro z hz d hd
    have hzq : starHom z ∈ pureBlock 1 := lift_image ▸ mem_map_of_mem starHom hz
    exact Subtype.ext (commonSpace_centralized z hzq d (mem_map_of_mem M.subtype hd))
  let : IsElementaryAbelian 2 (commonKernel ⊔ liftGroup : Subgroup M) :=
    IsElementaryAbelian.sup_of_le_centralizer hc
  rw [common_model_map]
  exact IsElementaryAbelian.map M.subtype

private theorem common_translate_first (z : M) (hz : IsConj a (z : Model))
    (i : Fin 3) (hq : starHom z = element (pureIndex 1 i))
    (d : M) (hd : d ∈ commonKernel) : IsConj a ((z*d : M) : Model) := by
  obtain ⟨n,hn⟩ := commonSpace_displacement i d hd
  have hs : z*z=1 := by
    apply Subtype.ext
    have h := hz.pow 2
    rw [show a^2=1 from orderOf_a ▸ pow_orderOf_eq_one a,isConj_one_right] at h
    simpa only [pow_two,Subgroup.coe_mul,Subgroup.coe_one] using h
  have hi : z⁻¹=z := inv_eq_of_mul_eq_one_left hs
  have hc := kernel_conjugation z n.val
  change z * kernelValue n.val * z⁻¹ =
    kernelValue (SylowCore.starMask (starHom z) n.val) at hc
  have hd' : d = z⁻¹ * kernelValue n.val * z * (kernelValue n.val)⁻¹ := by
    have hx (r s : ℕ) : kernelValue (r ^^^ s) = kernelValue r * kernelValue s := by
      simpa only [Nat.xor_eq] using kernelValue_xor r s
    rw [hn,hx,← hq,← hc,hi,
      inv_eq_of_mul_eq_one_left (kernelValue_square _)]
  have he : (MulAut.conj (kernelValue n.val)) z = z*d := by
    rw [hd']
    simp only [MulAut.conj_apply]
    group
  rw [← he]
  exact hz.trans (isConj_iff.mpr ⟨(kernelValue n.val : Model),rfl⟩)

/-- All nonidentity elements of the fixed native common group are first-class. -/
theorem commonModel_pure : ∀ v ∈ commonModel, v ≠ 1 → IsConj a v := by
  let := commonModel_elementary
  have hc : (liftGroup.map M.subtype) ≤ centralizer (commonSpace : Set Model) := by
    rintro _ ⟨z,hz,rfl⟩
    exact commonSpace_centralized z (lift_image ▸ mem_map_of_mem starHom hz)
  intro v hv hv1
  have he : commonModel = commonSpace ⊔ liftGroup.map M.subtype := by
    rw [common_model_map,Subgroup.map_sup]
    rfl
  rw [he] at hv
  have hv' : v ∈ (commonSpace : Set Model) * (liftGroup.map M.subtype : Set Model) := by
    rw [← coe_mul_of_right_le_normalizer_left commonSpace (liftGroup.map M.subtype)
      (hc.trans (centralizer_le_normalizer _))]
    exact hv
  obtain ⟨d,hd,t,⟨z,hz,rfl⟩,rfl⟩ := hv'
  have hzcomm := commonSpace_centralized z (lift_image ▸ mem_map_of_mem starHom hz) d hd
  change IsConj a (d * (z : Model))
  change d * (z : Model) ≠ 1 at hv1
  rw [hzcomm]
  obtain ⟨u,hu,rfl⟩ := hd
  rcases lift_coordinates z hz with rfl | rfl | rfl | rfl
  · simpa only [Subgroup.coe_one,one_mul] using
      commonSpace_pure _ (mem_map_of_mem M.subtype hu) (by simpa using hv1)
  · exact common_translate_first _ (commonLift_first 0) 0 (commonLift_projection 0) u hu
  · exact common_translate_first _ (commonLift_first 1) 1 (commonLift_projection 1) u hu
  · apply common_translate_first _ commonLift_product_first 2 _ u hu
    rw [map_mul,commonLift_projection,commonLift_projection]
    apply Subtype.ext
    decide +kernel

private theorem model_completion : commonCompletion commonModel = commonModel := sup_eq_left.mpr le_sup_left
private theorem pair_le_model : nativePair ≤ commonModel := nativePair_le_commonSpace.trans le_sup_left

/-- The native common group is its entire ambient centralizer. -/
theorem commonModel_self_centralizing : centralizer (commonModel : Set Model) = commonModel := by
  let := commonModel_elementary
  have h := commonCompletion_self_centralizing commonModel pair_le_model commonModel_image
  rwa [model_completion] at h

theorem commonModel_card : Nat.card commonModel = 128 := by
  let := commonModel_elementary
  have h := commonCompletion_card commonModel pair_le_model commonModel_image
  rwa [model_completion] at h

/-- Every pure common extension, including every order-two image and every
actual kernel, lies in the fixed native common group. -/
theorem common_extension_le_model (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) : X ≤ commonModel := by
  let := commonModel_elementary
  have hXM := (elementary_overgroup_placement X hpair).1
  intro v hv
  let z : M := ⟨v,hXM hv⟩
  by_cases hk : z ∈ max1Kernel
  · obtain ⟨m,hm⟩ := maskValue_surjective matrixA_mul_self matrixB_pow_four ⟨z,hk⟩
    have he : kernelValue m.val = z := congrArg Subtype.val hm
    obtain ⟨j,hj⟩ := common_kernel_coordinates X hpair hpure hpos hne m (he.symm ▸ hv)
    exact mem_sup_left ((mem_commonSpace _).mpr ⟨j,
      congrArg (fun u : M => (u : Model)) (he.symm.trans (congrArg kernelValue hj))⟩)
  · have hp1 : starHom z ≠ 1 := fun h => hk (starHom_ker ▸ MonoidHom.mem_ker.mpr h)
    obtain ⟨i,hi⟩ := pure_position_image_coordinates X hpair hpure 1 hpos _
      (mem_map_of_mem starHom hv) hp1
    obtain ⟨u,hu,huq⟩ := commonModel_image.symm ▸ pureIndex_mem 1 i
    have hv1 : v ≠ 1 := fun h => hk ((Subtype.ext h : z=1).symm ▸ max1Kernel.one_mem)
    have ht := common_first_fiber_mem commonModel pair_le_model commonModel_pure i u hu huq
      z (hpure v hv hv1) (hi.trans huq.symm)
    rwa [model_completion] at ht

/-- The actual double centralizer is controlled for every nontrivial common
image. The bound follows from a proved self-centralizing native group. -/
theorem common_double_centralizer_le_model (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (hne : (X.subgroupOf M).map starHom ≠ ⊥) :
    centralizer (centralizer (X : Set Model) : Set Model) ≤ commonModel := by
  let := commonModel_elementary
  have hX := common_extension_le_model X hpair hpure hpos hne
  have hH : commonModel ≤ centralizer (X : Set Model) :=
    commonModel.le_centralizer.trans (centralizer_le hX)
  have h := centralizer_le hH
  rwa [commonModel_self_centralizing] at h

theorem commonModel_rank_upper (v : Model) (hv : v ∈ commonModel) :
    pairRank (kernelValue 1257) v ≤ 16 := by
  let := commonModel_elementary
  apply commonCompletion_rank_upper commonModel pair_le_model commonModel_pure commonModel_image
  rwa [model_completion]

theorem commonModel_rank_unique (v : Model) (hv : v ∈ commonModel) (hv1 : v ≠ 1)
    (hr : ∀ j : Fin 8, pairRank v (kernelValue (commonCenterMask j)) ≤ 16) :
    v = (kernelValue 1257 : Model) := by
  let := commonModel_elementary
  apply commonCompletion_rank_unique commonModel pair_le_model commonModel_pure commonModel_image
    v _ hv1 hr
  rwa [model_completion]

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
