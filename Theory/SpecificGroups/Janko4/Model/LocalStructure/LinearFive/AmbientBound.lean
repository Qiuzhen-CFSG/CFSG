module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Coordinates
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second

/-!
# The ambient centralizer of the native F lies in max1

A sixteen-letter word in max1 conjugates the certified seed to kernel mask 51,
the first generator of F. The whole seed centralizer lies in max1, so the same
is true of the whole centralizer of F. This is the first ambient step in the
self-centralization argument, without an ambient enumeration or cover premise.
Source: Kleidman--Wilson (1988), p.490; the seed centralizer is certified by
`InvolutionCentralizers.Second`.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount QuotientCount.Image
open Simplicity.Max1Fusion.KernelOrbits
open Subgroup
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed basis

def pathWord : List Bool → M
  | [] => 1
  | b :: bs => (if b then localY matrixA_mul_self matrixB_pow_four
      else localX matrixA_mul_self matrixB_pow_four) * pathWord bs
private def pathMask : List Bool → ℕ → ℕ
  | [], m => m
  | b :: bs, m => pathMask bs (maskImage (if b then yMasks else xMasks) m)

private theorem pathWord_conjugates (bs : List Bool) (m : ℕ) :
    (pathWord bs)⁻¹ * kernelValue m * pathWord bs = kernelValue (pathMask bs m) := by
  induction bs generalizing m with
  | nil => simp only [pathWord, inv_one, one_mul, mul_one, pathMask]
  | cons b bs ih =>
    rw [pathWord]
    let c : M := if b then localY matrixA_mul_self matrixB_pow_four
      else localX matrixA_mul_self matrixB_pow_four
    have hc : c⁻¹ * kernelValue m * c =
        kernelValue (maskImage (if b then yMasks else xMasks) m) := by
      cases b
      · exact right_conj_mask_x _ _ m
      · exact right_conj_mask_y _ _ m
    calc
      _ = (pathWord bs)⁻¹ * (c⁻¹ * kernelValue m * c) * pathWord bs := by
        dsimp only [c]
        group
      _ = _ := by rw [hc, ih]; rfl

def kernelFusionWord : M :=
  pathWord [true, false, true, true, false, true, false, true,
    true, false, true, false, true, false, true, false]

theorem kernelFusionWord_conjugates :
    kernelFusionWord⁻¹ * kernelValue 1 * kernelFusionWord = kernelValue 51 := by
  rw [kernelFusionWord, pathWord_conjugates]
  congr 1

/-- The parallel first-class fusion path for the second native F generator. -/
def kernelPairFusionWord : M :=
  pathWord [true, false, true, false, true, false, true, true, false, true,
    true, false, true, false, true, true, false, true, true, false, true, true,
    false, true]

theorem kernelPairFusionWord_conjugates :
    kernelPairFusionWord⁻¹ * kernelValue 3 * kernelPairFusionWord = kernelValue 73 := by
  rw [kernelPairFusionWord, pathWord_conjugates]
  exact congrArg kernelValue (by decide +kernel)

theorem centralizer_kernel51_le_M :
    centralizer ({(kernelValue 51 : Model)} : Set Model) ≤ M := by
  intro z hz
  let c : Model := kernelFusionWord
  have he : c⁻¹ * (kernelValue 1 : Model) * c = (kernelValue 51 : Model) :=
    congrArg (fun w : M => (w : Model)) kernelFusionWord_conjugates
  have hz' : z * (c⁻¹ * (kernelValue 1 : Model) * c) =
      (c⁻¹ * (kernelValue 1 : Model) * c) * z := by
    rw [he]
    exact mem_centralizer_singleton_iff.mp hz
  have hc : c * z * c⁻¹ ∈
      centralizer ({(kernelValue 1 : Model)} : Set Model) := by
    apply mem_centralizer_singleton_iff.mpr
    calc
      _ = c * (z * (c⁻¹ * (kernelValue 1 : Model) * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * (kernelValue 1 : Model) * c) * z) * c⁻¹ := by rw [hz']
      _ = _ := by group
  have hseed : kernelValue 1 = localKernelSeed matrixA_mul_self matrixB_pow_four :=
    maskValue_one _ _
  have hin : c * z * c⁻¹ ∈ M := by
    apply InvolutionCentralizers.Second.ambient_le_max1
    change c * z * c⁻¹ ∈ centralizer ({(localKernelSeed matrixA_mul_self matrixB_pow_four : Model)} : Set Model)
    simpa only [hseed] using hc
  have hcM : c ∈ M := kernelFusionWord.property
  have hzM := M.mul_mem (M.mul_mem (M.inv_mem hcM) hin) hcM
  simpa only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hzM

theorem centralizer_F_le_M : centralizer (F : Set Model) ≤ M := by
  apply le_trans ?_ centralizer_kernel51_le_M
  apply centralizer_le
  intro z hz
  have hz' : z = (kernelValue 51 : Model) := Set.mem_singleton_iff.mp hz
  subst z
  exact generator_mem_F 0

end Janko4.LocalStructure.LinearFive
