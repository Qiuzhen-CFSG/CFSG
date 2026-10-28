module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions.CommonModel
import Mathlib.Tactic.Group

/-!
# Intrinsic rank separation in the common kernel

Explicit Mathieu words carry every common-kernel pair with mask 1257
onto a previously certified rank-sixteen pair. Every other nonidentity
common-kernel element has rank twenty against one of the forced central
eight elements. Only the small eleven-bit actions are checked here; no
new 112-dimensional rank computation is needed.

This supplies the kernel part of the intrinsic distinguished-involution
criterion for actual double centralizers in KW (1988), Section 2.1, p.489.
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

private theorem alphabet_projection (i : Fin 4) :
    (starHom (commonAlphabet i)).val = alphabet i := by
  fin_cases i
  · exact actionImageEquivStarGroup_x _ _
  · exact actionImageEquivStarGroup_y _ _
  · change (starHom (localX matrixA_mul_self matrixB_pow_four)⁻¹).val = starX⁻¹
    rw [map_inv]
    exact congrArg Inv.inv (actionImageEquivStarGroup_x _ _)
  · change (starHom (localY matrixA_mul_self matrixB_pow_four)⁻¹).val = starY⁻¹
    rw [map_inv]
    exact congrArg Inv.inv (actionImageEquivStarGroup_y _ _)

theorem common_word_projection (w : List (Fin 4)) :
    (starHom (evalWord commonAlphabet w)).val = evalWord alphabet w := by
  induction w with
  | nil => simp only [evalWord,map_one,Subgroup.coe_one]
  | cons i w ih => simp only [evalWord,map_mul,Subgroup.coe_mul,alphabet_projection,ih]


@[expose] def commonWordMask (w : List (Fin 4)) (m : ℕ) : ℕ :=
  maskImage
    (fun i => pairLabel ((evalWord alphabet w) (basisPair i).1)
      ((evalWord alphabet w) (basisPair i).2)) m

theorem common_word_conjugation (w : List (Fin 4)) (m : ℕ) :
    (MulAut.conj ((evalWord commonAlphabet w : M) : Model)) (kernelValue m : Model) =
      (kernelValue (commonWordMask w m) : Model) := by
  have h := kernel_conjugation (evalWord commonAlphabet w) m
  change _ = kernelValue (SylowCore.starMask (starHom (evalWord commonAlphabet w)) m) at h
  simp only [SylowCore.starMask,common_word_projection] at h
  exact congrArg (fun u : M => (u : Model)) h

private theorem word_pairRank (w : List (Fin 4)) (m n : ℕ) :
    pairRank (kernelValue (commonWordMask w m)) (kernelValue (commonWordMask w n)) =
      pairRank (kernelValue m) (kernelValue n) := by
  have h := pairRank_conj ((evalWord commonAlphabet w : M) : Model) (kernelValue m) (kernelValue n)
  rwa [common_word_conjugation,common_word_conjugation] at h

private def upperWord : Fin 32 → List (Fin 4) := ![[],[1,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,1],[3,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,3,0,1,0,3],[0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,3,0,1,0,3,0,3,0,3,0,3],[3,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3],[1,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,1],[1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,1],[0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,3,0,1,0,3,0],[0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,3,0],[1,0,3,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,1],[3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1],[1,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,3],[1,0,1,0,1,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,1,0,3,0],[1,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,3],[3,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,1,0,1],[0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,1,0,1,0,1,0,3,0,1,0,3,0,3,0],[],[0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,3,0,1],[3,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3],[1,0,3,0,1,0,1,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,1],[0,3,0,3,0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,1],[3,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,1],[0,3,0,3,0,1,0,1,0,1,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0],[0,1,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,1,0,3,0,1],[0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,3],[1,0,1,0,1,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,1,0,3,0,3,0,3],[1,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,3],[3,0,1,0,3,0,3,0,1,0,1,0,1,0,1,0,1,0,3,0,1,0,1,0],[3,0,1,0,1,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,3,0,3,0,1],[3,0,1,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,3,0],[1,0,3,0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,3,0,1],[0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0]]

private def lowerWord : Fin 32 → List (Fin 4) := ![[],[3,0,1,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,3],[1,0,3,0,3,0,3,0,1,0,1,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,3,0,1,0,1],[0,3,0,3,0,3,0,1,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0,1,0,1,0,1,0,3,0],[3,0,1,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1],[3,0,1,0,3,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,3,0,1,0,1,0],[3,0,1,0,1,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,1,0,3,0],[0,1,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0],[1,0,3,0,3,0,1,0,1,0,3,0,3,0,1,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,3],[3,0,1,0,1,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,1],[1,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,1,0,1],[0,3,0,3,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,1,0],[0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,3],[1,0,1,0,3,0,3,0,3,0,3,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,1,0,3],[3,0,3,0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0],[1,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,3,0],[],[0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0],[1,0,3,0,1,0,1,0,1,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0],[0,1,0,1,0,3,0,1,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,3,0,3,0,3,0,1,0],[0,3,0,3,0,3,0,1,0,1,0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,1,0,1,0,1],[1,0,1,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,3,0,3,0,1,0,3,0,1,0,1,0],[1,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,3,0,1,0,1],[0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,3,0,3,0,1,0,1,0,3,0,1,0,3,0,3,0,1,0,1,0,3,0],[3,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0,1,0,1,0,3,0,3,0,1,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0],[3,0,3,0,1,0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,1,0],[3,0,3,0,3,0,3,0,3,0,1,0,3,0,3,0,3,0,1,0,3,0,1,0,3,0,1,0,1,0,1,0,1,0,1],[0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,1,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0,3,0],[0,3,0,3,0,3,0,1,0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,1,0,1,0,3,0,1,0,1,0,1,0,3],[3,0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,3,0,3,0,3,0,3,0,1,0,1,0,1,0,1,0,3,0,1,0,3,0,3,0],[1,0,3,0,1,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,1,0,3,0,3,0,1,0,3,0,3,0,1,0,1,0],[3,0,1,0,1,0,3,0,3,0,3,0,1,0,1,0,3,0,1,0,1,0,3,0,3,0,3,0,1,0,3,0,3,0]]

private def witnessIndex : Fin 32 → Fin 8 := ![0,1,2,1,2,1,2,1,1,1,1,1,1,1,1,1,0,1,2,1,2,1,2,1,1,1,1,1,1,1,1,1]

private theorem upper_action : ∀ i : Fin 32, i ≠ 0 → i ≠ 16 →
    commonWordMask (upperWord i) 457 = 1257 ∧
    commonWordMask (upperWord i) 641 = displacementMask 0 0 i := by decide +kernel

private theorem lower_action : ∀ i : Fin 32, i ≠ 0 → i ≠ 16 →
    commonWordMask (lowerWord i) 818 = displacementMask 0 0 i ∧
    commonWordMask (lowerWord i) 1449 = commonCenterMask (witnessIndex i) := by decide +kernel

private theorem pairRank_kernel_self (m : ℕ) : pairRank (kernelValue m) (kernelValue m) = 0 := by
  have hs : toMatrix (kernelValue m : Model) * toMatrix (kernelValue m : Model) = 1 := by
    rw [← map_mul]
    simpa only [Subgroup.coe_mul,Subgroup.coe_one,map_one] using
      congrArg (fun u : M => toMatrix (u : Model)) (kernelValue_square m)
  have he : (toMatrix (kernelValue m : Model) - 1) *
      (toMatrix (kernelValue m : Model) - 1) = 0 := by
    have add (A B : Matrix (Fin 112) (Fin 112) (ZMod 2)) : A - B = A + B := by
      ext i j
      exact ZModModule.sub_eq_add _ _
    simp only [add,add_mul,mul_add,mul_one,one_mul,hs]
    have two (A : Matrix (Fin 112) (Fin 112) (ZMod 2)) : A + A = 0 := by
      rw [← add,sub_self]
    rw [show (1 : Matrix (Fin 112) (Fin 112) (ZMod 2)) + toMatrix (kernelValue m : Model) +
        (toMatrix (kernelValue m : Model) + 1) =
        (1 + 1) + (toMatrix (kernelValue m : Model) + toMatrix (kernelValue m : Model)) by abel]
    rw [two,two,zero_add]
  exact congrArg Matrix.rank he |>.trans Matrix.rank_zero

/-- Every common-kernel element has small pair rank against the distinguished
involution, with the literal original binary-kernel embedding. -/
theorem common_kernel_rank_upper (i : Fin 32) :
    pairRank (kernelValue 1257) (kernelValue (displacementMask 0 0 i)) ≤ 16 := by
  by_cases hi : i = 0
  · subst i
    change pairRank (kernelValue 1257) (kernelValue 0) ≤ 16
    simp [pairRank,kernelValue_zero]
  by_cases hj : i = 16
  · subst i
    change pairRank (kernelValue 1257) (kernelValue 1257) ≤ 16
    rw [pairRank_kernel_self]
    decide
  have h := word_pairRank (upperWord i) 457 641
  rw [(upper_action i hi hj).1,(upper_action i hi hj).2] at h
  rw [h]
  exact ninth_kernel_pairRank_le 0 1

/-- Every other nonidentity common-kernel element is separated by one of
the eight elements forced into the ACTUAL double centralizer. -/
theorem common_kernel_rank_witness (i : Fin 32) (h0 : i ≠ 0) (h16 : i ≠ 16) :
    ∃ j : Fin 8, pairRank (kernelValue (displacementMask 0 0 i))
      (kernelValue (commonCenterMask j)) = 20 := by
  refine ⟨witnessIndex i,?_⟩
  have h := word_pairRank (lowerWord i) 818 1449
  rwa [(lower_action i h0 h16).1,(lower_action i h0 h16).2,native_pairRank] at h

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativeExtensions
