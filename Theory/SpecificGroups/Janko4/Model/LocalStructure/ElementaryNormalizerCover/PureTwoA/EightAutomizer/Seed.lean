module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Words
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Geometry.KernelOrbit

/-!
# The native seed belongs to the same conjugate F-normalizer

The literal conjugator sends the seed to kernel mask 1173. Its commutators
with the four F-lifts lie in the common fixed kernel, hence in F. All these
calculations use eleven-bit kernel coordinates, avoiding further dense matrix
certificates. The second-class orbit will transport this membership to a
generating set of the whole native eight.
Source: Kleidman--Wilson (1988), Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
set_option Elab.async false
public noncomputable section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Subgroup Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
open LinearFive
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis lift

private def localLetter : Fin 2 → M :=
  ![localX matrixA_mul_self matrixB_pow_four,localY matrixA_mul_self matrixB_pow_four]
private def letterAction : Fin 2 → ℕ → ℕ := ![maskImage xMasks,maskImage yMasks]
private def localWord (w : List (Fin 2)) : M := (w.map localLetter).prod
private def wordAction (w : List (Fin 2)) (m : ℕ) : ℕ := w.foldl (fun n i => letterAction i n) m

private theorem letter_conjugates (i : Fin 2) (m : ℕ) :
    (localLetter i)⁻¹ * kernelValue m * localLetter i = kernelValue (letterAction i m) := by
  fin_cases i
  · exact right_conj_mask_x _ _ m
  · exact right_conj_mask_y _ _ m

private theorem word_conjugates (w : List (Fin 2)) (m : ℕ) :
    (localWord w)⁻¹ * kernelValue m * localWord w = kernelValue (wordAction w m) := by
  induction w generalizing m with
  | nil => simp [localWord,wordAction]
  | cons i w ih =>
    change (localLetter i * localWord w)⁻¹ * kernelValue m *
      (localLetter i * localWord w) = _
    calc
      _ = (localWord w)⁻¹ * ((localLetter i)⁻¹ * kernelValue m * localLetter i) *
          localWord w := by group
      _ = _ := by rw [letter_conjugates,ih]; rfl

private def conjugatorLetters : List (Fin 2) :=
  [0,1,1,0,1,1,0,1,1,0,1,1,0,1,0]
private def localConjugator : M := localWord conjugatorLetters * kernelValue 1

private theorem seed_eq : ElementaryEightGeometry.Loewy.nativeGenerator 0 =
    (kernelValue 1 : Model) := by
  change (ElementaryEightGeometry.nativeMask 1 : Model) = _
  rfl

private theorem coe_localConjugator : (localConjugator : Model) = c := by
  simp only [localConjugator,localWord,conjugatorLetters,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,mul_one,localLetter,Matrix.cons_val_zero,
    Matrix.cons_val_one,Subgroup.coe_mul]
  rw [← seed_eq]
  dsimp only [c,cxyx,cxy,cx,p4,p2,xyy,xy,sourceX,sourceY]
  group

private theorem localConjugator_seed :
    localConjugator⁻¹ * kernelValue 1 * localConjugator = kernelValue 1173 := by
  have hc : wordAction conjugatorLetters 1 = 1173 := by decide +kernel
  calc
    _ = (kernelValue 1)⁻¹ *
        ((localWord conjugatorLetters)⁻¹ * kernelValue 1 * localWord conjugatorLetters) *
        kernelValue 1 := by simp only [localConjugator]; group
    _ = (kernelValue 1)⁻¹ * kernelValue 1173 * kernelValue 1 := by
      rw [word_conjugates,hc]
    _ = kernelValue 1173 := by
      rw [mul_assoc,(kernelValue_commute 1173 1).eq,inv_mul_cancel_left]

private def displacement (i : Fin 4) : ℕ := maskImage (liftKernelMasks i) 1173 ^^^ 1173

private theorem displacement_fixed (i j : Fin 4) :
    maskImage (liftKernelMasks j) (displacement i) = displacement i := by
  have h : ∀ i j : Fin 4,
      maskImage (liftKernelMasks j) (displacement i) = displacement i := by decide +kernel
  exact h i j

private theorem kernel1173_normalizes : kernelValue 1173 ∈ normalizer (localF : Set M) := by
  apply LinearFive.Geometry.kernelValue_normalizes_of_fixed
  exact displacement_fixed

/-- The actual native seed belongs to the exact conjugate used by all three actors. -/
theorem seed_mem_target : ElementaryEightGeometry.Loewy.nativeGenerator 0 ∈ target := by
  have hm : (kernelValue 1173 : Model) ∈ normalizer (F : Set Model) :=
    (Subgroup.le_normalizer_map M.subtype)
      (Subgroup.mem_map.mpr ⟨kernelValue 1173,kernel1173_normalizes,rfl⟩)
  have he : c⁻¹ * (kernelValue 1 : Model) * c = (kernelValue 1173 : Model) := by
    simpa only [Subgroup.coe_mul,Subgroup.coe_inv,coe_localConjugator] using
      congrArg (fun x : M => (x : Model)) localConjugator_seed
  apply Subgroup.mem_map.mpr
  refine ⟨(kernelValue 1173 : Model),hm,?_⟩
  change c * (kernelValue 1173 : Model) * c⁻¹ = _
  rw [← he,seed_eq]
  group

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
