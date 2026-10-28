module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LinearFive.Normalizer.Mask
public import Theory.Representation.SL5ExteriorSquare.TwoGeneratorRecognition

/-!
# Actual binary coordinates of the native linear-five subgroup

The ten independent native generators identify F with ten binary coordinates.
This parametrization will be composed with the explicitly checked exterior
change of basis; dimension alone does not identify the conjugation action.
-/

@[expose] public noncomputable section
namespace Janko4.LocalStructure.LinearFive
open Cardinality KernelCount
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel localX localY

abbrev FC := Fin 10 → ZMod 2

def maskVector (m : ℕ) : FC := fun i => if m.testBit i.val then 1 else 0

private theorem bit_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide

private theorem bit_inj : Function.Injective (fun a : ZMod 2 => decide (a = 1)) := by
  decide +kernel

def nativeParamHom : Multiplicative FC →* F where
  toFun v := ⟨(binaryProduct generators (fun i => decide (v.toAdd i = 1)) : M),
    (mem_F_iff_binaryProduct _).mpr ⟨_, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    change (binaryProduct generators (fun i => decide ((0 : FC) i = 1)) : M).val = 1
    simpa only [Pi.zero_apply, show (decide ((0 : ZMod 2) = 1)) = false from rfl,
      Subgroup.coe_one] using
      congrArg (fun g : M => (g : Model)) (binaryProduct_zero generators)
  map_mul' v w := by
    apply Subtype.ext
    change (binaryProduct generators (fun i => decide ((v.toAdd + w.toAdd) i = 1)) : M).val =
      (binaryProduct generators (fun i => decide (v.toAdd i = 1)) : M).val *
      (binaryProduct generators (fun i => decide (w.toAdd i = 1)) : M).val
    simpa only [Pi.add_apply, bit_add, Subgroup.coe_mul] using
      (congrArg (fun g : M => (g : Model)) (binaryProduct_mul generators
        generators_square generators_commute (fun i => decide (v.toAdd i = 1))
          (fun i => decide (w.toAdd i = 1)))).symm

theorem nativeParamHom_bijective : Function.Bijective nativeParamHom := by
  constructor
  · intro v w h
    have he : (nativeParamHom v : Model) = (nativeParamHom w : Model) :=
      congrArg (fun x : F => (x : Model)) h
    have hg : binaryProduct generators (fun i => decide (v.toAdd i = 1)) =
        binaryProduct generators (fun i => decide (w.toAdd i = 1)) :=
      Subtype.ext he
    have hv := generators_binaryProduct_injective hg
    apply Multiplicative.toAdd.injective
    funext i
    exact bit_inj (congrFun hv i)
  · intro x
    obtain ⟨v,hv⟩ := (mem_F_iff_binaryProduct (x : Model)).mp x.property
    refine ⟨Multiplicative.ofAdd (fun i => if v i then (1 : ZMod 2) else 0), ?_⟩
    apply Subtype.ext
    change (binaryProduct generators (fun i => decide ((if v i then (1 : ZMod 2) else 0) = 1)) : M).val = x.val
    have he : (fun i => decide ((if v i then (1 : ZMod 2) else 0) = 1)) = v := by
      funext i
      cases v i <;> decide
    rw [he]
    exact hv

def nativeParam : Multiplicative FC ≃* F := MulEquiv.ofBijective nativeParamHom nativeParamHom_bijective

def fGenerator (i : Fin 10) : F := ⟨generators i, generator_mem_F i⟩

theorem nativeParam_mask (m : ℕ) :
    (nativeParam (Multiplicative.ofAdd (maskVector m)) : Model) = fValue m := by
  change (binaryProduct generators (fun i => decide ((maskVector m) i = 1)) : M).val =
    (binaryProduct generators (fun i => m.testBit i.val) : M).val
  congr 2
  funext i
  cases h : m.testBit i.val <;> simp only [maskVector, h] <;> decide

theorem nativeParam_single (i : Fin 10) :
    nativeParam (Multiplicative.ofAdd (Pi.single i 1)) = fGenerator i := by
  have he : maskVector (2^i.val) = Pi.single i 1 := by
    funext j
    by_cases h : i = j
    · subst j
      simp [maskVector]
    · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
      simp [maskVector, hv, h]
  apply Subtype.ext
  rw [← he, nativeParam_mask, fValue_basis]
  rfl

end Janko4.LocalStructure.LinearFive
