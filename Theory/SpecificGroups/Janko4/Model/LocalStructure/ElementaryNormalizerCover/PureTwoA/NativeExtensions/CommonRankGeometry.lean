module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonModel
import Mathlib.Tactic.Group

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonKernelRanks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonLiftRanks

/-!
# Rank geometry for every actual common-image lift

The three nonidentity image fibers are represented by explicit conjugates
of x. Kernel transitivity fixes all kernel witnesses while transporting
every actual first-class lift to its representative. Together with the
kernel rank separation, this characterizes mask 1257 intrinsically inside
the actual double centralizer whenever the image is the common four-group.

No lift or kernel is assumed preserved by the whole normalizer. The
subsequent normalizer application uses only simultaneous-conjugacy
invariance of rank. Source: KW (1988), Section 2.1, p.489.
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

private def rankLiftWord : Fin 3 → List (Fin 4) := ![[0,1,0,3,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,1],[0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,3,0,1],[0,3,0,3,0,1,0,3,0,1,0,3,0,3,0,1,0,1,0,3,0,3,0,3]]

private def rankLift (i : Fin 3) : M :=
  (MulAut.conj (evalWord commonAlphabet (rankLiftWord i)))
    (localX matrixA_mul_self matrixB_pow_four)

private theorem rankLift_projection (i : Fin 3) :
    starHom (rankLift i) = element (pureIndex 1 i) := by
  apply Subtype.ext
  have hx : (starHom (localX matrixA_mul_self matrixB_pow_four)).val = starX :=
    actionImageEquivStarGroup_x _ _
  simp only [rankLift,MulAut.conj_apply,map_mul,map_inv,Subgroup.coe_mul,
    Subgroup.coe_inv,common_word_projection,hx]
  revert i
  decide +kernel

private theorem rankLift_first (i : Fin 3) : IsConj a (rankLift i : Model) := by
  have hx := (outside_first_iff 0).mpr (Or.inl rfl)
  have he : outsideRepresentative matrixA_mul_self matrixB_pow_four 0 =
      localX matrixA_mul_self matrixB_pow_four := by
    simp [outsideRepresentative,outsideMask,binaryProduct_zero]
  rw [he] at hx
  exact hx.trans (isConj_iff.mpr
    ⟨((evalWord commonAlphabet (rankLiftWord i) : M) : Model),rfl⟩)

private def lowerMask : Fin 3 → ℕ := ![195,768,768]

private theorem lift_action : ∀ i : Fin 3,
    commonWordMask (rankLiftWord i) 96 = 1257 ∧
    commonWordMask (rankLiftWord i) (lowerMask i) = 320 := by decide +kernel

private theorem rankLift_ranks (i : Fin 3) :
    pairRank (rankLift i) (kernelValue 1257) = 16 ∧
    pairRank (rankLift i) (kernelValue 320) = 20 := by
  have upper := pairRank_conj ((evalWord commonAlphabet (rankLiftWord i) : M) : Model)
    (localX matrixA_mul_self matrixB_pow_four) (kernelValue 96)
  rw [common_word_conjugation,(lift_action i).1,common_lift_rank_96] at upper
  have lower := pairRank_conj ((evalWord commonAlphabet (rankLiftWord i) : M) : Model)
    (localX matrixA_mul_self matrixB_pow_four) (kernelValue (lowerMask i))
  rw [common_word_conjugation,(lift_action i).2] at lower
  have hl : pairRank (localX matrixA_mul_self matrixB_pow_four) (kernelValue (lowerMask i)) = 20 := by
    fin_cases i
    · exact common_lift_rank_195
    · exact common_lift_rank_768
    · exact common_lift_rank_768
  exact ⟨upper,lower.trans hl⟩

private theorem kernel_conj_fixes (u : M) (hu : u ∈ max1Kernel) (m : ℕ) :
    (MulAut.conj (u : Model)) (kernelValue m : Model) = (kernelValue m : Model) := by
  let : IsElementaryAbelian 2 max1Kernel := localKernel_elementary _ _
  have hc := max1Kernel.le_centralizer hu _ (maskValue matrixA_mul_self matrixB_pow_four m).property
  have he : u * kernelValue m * u⁻¹ = kernelValue m := by
    rw [← hc,mul_inv_cancel_right]
  exact congrArg (fun v : M => (v : Model)) he

/-- Exact ranks for EVERY actual first-class lift in every nontrivial common
fiber. The binary-kernel conjugator fixes both comparison elements. -/
theorem common_extension_outside_ranks (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (hpos : (X.subgroupOf M).map starHom ≤ imageBlock 1)
    (z : M) (hz : (z : Model) ∈ X) (hk : z ∉ max1Kernel) :
    pairRank z (kernelValue 1257) = 16 ∧ pairRank z (kernelValue 320) = 20 := by
  have hn : starHom z ≠ 1 := fun he => hk (starHom_ker ▸ MonoidHom.mem_ker.mpr he)
  obtain ⟨i,hi⟩ := pure_position_image_coordinates X hpair hpure 1 hpos
    (starHom z) (mem_map_of_mem starHom hz) hn
  obtain ⟨u,hu,he⟩ := pure_extension_lift_fiber_transitive X hpair hpure z hz hk
    (rankLift i) (rankLift_first i) ((rankLift_projection i).trans hi.symm)
  have hr (m : ℕ) : pairRank (rankLift i) (kernelValue m) = pairRank z (kernelValue m) := by
    have h := pairRank_conj (u : Model) (z : Model) (kernelValue m)
    rw [kernel_conj_fixes u hu] at h
    have he' : (MulAut.conj (u : Model)) (z : Model) = (rankLift i : Model) :=
      congrArg (fun v : M => (v : Model)) he
    rwa [he'] at h
  exact ⟨(hr 1257).symm.trans (rankLift_ranks i).1,(hr 320).symm.trans (rankLift_ranks i).2⟩

private theorem pairRank_commute {x y : Model} (hc : Commute x y) :
    pairRank x y = pairRank y x := by
  unfold pairRank
  apply congrArg Matrix.rank
  have he := congrArg toMatrix hc.eq
  simp only [map_mul] at he
  simp only [sub_mul,mul_sub,mul_one,one_mul]
  rw [he]
  abel

private theorem common_block_le : pureBlock 1 ≤ imageBlock 1 := by
  apply (closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  apply (mem_imageBlock_iff _ _).mpr
  fin_cases i
  · exact ⟨4,rfl⟩
  · exact ⟨11,rfl⟩

/-- Rank bound for every element of the full actual completion, including
all possible lift and kernel choices. -/
theorem commonCompletion_rank_upper (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1)
    (v : Model) (hv : v ∈ commonCompletion X) :
    pairRank (kernelValue 1257) v ≤ 16 := by
  have hXM := (elementary_overgroup_placement X hpair).1
  have hHM : commonCompletion X ≤ M :=
    sup_le hXM (commonSpace_le_kernel.trans (map_subtype_le _))
  let : IsElementaryAbelian 2 (commonCompletion X) := commonCompletion_elementary X hXM himage.le
  let z : M := ⟨v,hHM hv⟩
  by_cases hk : z ∈ max1Kernel
  · have hc : v ∈ commonSpace := by
      rw [← commonCompletion_kernel X hpair himage]
      exact ⟨hv,mem_map_of_mem M.subtype hk⟩
    obtain ⟨i,rfl⟩ := (mem_commonSpace v).mp hc
    exact common_kernel_rank_upper i
  · have hn : (X.subgroupOf M).map starHom ≠ ⊥ := by
      rw [himage]
      intro he
      have h := pureBlock_card 1
      rw [he,card_bot] at h
      contradiction
    have hu := (common_extension_outside_ranks (commonCompletion X)
      (hpair.trans le_sup_left) (commonCompletion_pure X hpair hpure himage.le hn)
      (by rw [commonCompletion_image X hXM,himage]; exact common_block_le) z hv hk).1
    have hc : Commute (kernelValue 1257 : Model) v :=
      (commonCompletion X).le_centralizer hv _
        (mem_sup_right ((mem_commonSpace _).mpr ⟨16,rfl⟩))
    rw [pairRank_commute hc]
    exact hu.le

/-- Among nonidentity elements of the actual completion, the forced central
eight distinguishes mask 1257 uniquely. -/
theorem commonCompletion_rank_unique (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hpair : nativePair ≤ X) (hpure : ∀ v ∈ X, v ≠ 1 → IsConj a v)
    (himage : (X.subgroupOf M).map starHom = pureBlock 1)
    (v : Model) (hv : v ∈ commonCompletion X) (hv1 : v ≠ 1)
    (hr : ∀ j : Fin 8, pairRank v (kernelValue (commonCenterMask j)) ≤ 16) :
    v = (kernelValue 1257 : Model) := by
  have hXM := (elementary_overgroup_placement X hpair).1
  have hHM : commonCompletion X ≤ M :=
    sup_le hXM (commonSpace_le_kernel.trans (map_subtype_le _))
  let : IsElementaryAbelian 2 (commonCompletion X) := commonCompletion_elementary X hXM himage.le
  let z : M := ⟨v,hHM hv⟩
  by_cases hk : z ∈ max1Kernel
  · have hc : v ∈ commonSpace := by
      rw [← commonCompletion_kernel X hpair himage]
      exact ⟨hv,mem_map_of_mem M.subtype hk⟩
    obtain ⟨i,rfl⟩ := (mem_commonSpace v).mp hc
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hv1 (congrArg (fun u : M => (u : Model)) kernelValue_zero)
    by_cases hi16 : i = 16
    · subst i; rfl
    obtain ⟨j,hj⟩ := common_kernel_rank_witness i hi0 hi16
    have hh := hr j
    rw [hj] at hh
    omega
  · have hn : (X.subgroupOf M).map starHom ≠ ⊥ := by
      rw [himage]
      intro he
      have h := pureBlock_card 1
      rw [he,card_bot] at h
      contradiction
    have hu := (common_extension_outside_ranks (commonCompletion X)
      (hpair.trans le_sup_left) (commonCompletion_pure X hpair hpure himage.le hn)
      (by rw [commonCompletion_image X hXM,himage]; exact common_block_le) z hv hk).2
    have hh := hr 1
    change pairRank z (kernelValue 320) ≤ 16 at hh
    rw [hu] at hh
    omega

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
