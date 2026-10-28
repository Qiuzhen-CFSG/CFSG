module
public import Theory.Representation.BinaryPermutationEightCover.CodeGeometry
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Affine translations on the original four-dimensional code

The affine evaluation coordinates construct a permutation for every linear
functional vanishing on the constant word. It acts on the code by
v ↦ v + φ(v)·1. Each nonidentity translation is fixed-point-free of order
two on eight coordinates, so it is even. Thus all these transvections
belong to the literal A₈ stabilizer of the code.

Source: Aschbacher–Smith Lemma 12.3.3, printed p.808. The subsequent
normal-kernel argument places these elements in the stabilizer's two-core.
-/

@[expose] public noncomputable section
open Module
namespace BinaryPermutation.EightCore
variable (U : Submodule (ZMod 2) (core (Fin 8)))
  (hd : finrank (ZMod 2) U = 4) (hone : oneWord ∈ U)
  (hw : ∀ v ∈ U, v ≠ 0 → v ≠ oneWord → wordWeight v.val = 4)

def codeTranslation (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) :
    Equiv.Perm (Fin 8) :=
  let E := codeAffineCoordinates U hd hone hw
  let τ : Equiv.Perm {ψ : Module.Dual (ZMod 2) U // ψ ⟨oneWord,hone⟩ = 1} :=
    { toFun := fun ψ => ⟨ψ.val + φ, by rw [LinearMap.add_apply,ψ.property,hφ,add_zero]⟩
      invFun := fun ψ => ⟨ψ.val + φ, by rw [LinearMap.add_apply,ψ.property,hφ,add_zero]⟩
      left_inv := by intro ψ; apply Subtype.ext; ext v; exact CharTwo.add_cancel_right _ _
      right_inv := by intro ψ; apply Subtype.ext; ext v; exact CharTwo.add_cancel_right _ _ }
  (E.trans τ).trans E.symm

theorem codeTranslation_coordinate
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) (i : Fin 8) (v : U) :
    v.val.val (codeTranslation U hd hone hw φ hφ i) = v.val.val i + φ v := by
  let E := codeAffineCoordinates U hd hone hw
  have h : (E (codeTranslation U hd hone hw φ hφ i)).val = (E i).val + φ := by
    change (E (E.symm _)).val = _
    rw [E.apply_symm_apply]
    rfl
  exact LinearMap.congr_fun h v

theorem codeTranslation_sq
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) :
    (codeTranslation U hd hone hw φ hφ) ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  apply code_evaluation_injective U hd hw
  funext v
  change v.val.val (codeTranslation U hd hone hw φ hφ
    (codeTranslation U hd hone hw φ hφ i)) = v.val.val i
  rw [codeTranslation_coordinate,codeTranslation_coordinate]
  exact CharTwo.add_cancel_right _ _

theorem codeTranslation_even
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) :
    codeTranslation U hd hone hw φ hφ ∈ alternatingGroup (Fin 8) := by
  classical
  rw [Equiv.Perm.mem_alternatingGroup]
  by_cases hz : φ = 0
  · have he : codeTranslation U hd hone hw φ hφ = 1 := by
      apply Equiv.ext
      intro i
      apply code_evaluation_injective U hd hw
      funext v
      change v.val.val (codeTranslation U hd hone hw φ hφ i) = v.val.val i
      rw [codeTranslation_coordinate,hz,LinearMap.zero_apply,add_zero]
    rw [he,map_one]
  · have hn : IsEmpty (Function.fixedPoints (codeTranslation U hd hone hw φ hφ)) := by
      constructor
      rintro ⟨i,hi⟩
      apply hz
      ext v
      have he := codeTranslation_coordinate U hd hone hw φ hφ i v
      change codeTranslation U hd hone hw φ hφ i = i at hi
      rw [hi] at he
      exact (add_eq_left.mp he.symm)
    let := hn
    rw [Equiv.Perm.sign_of_pow_two_eq_one (codeTranslation_sq U hd hone hw φ hφ)]
    norm_num

theorem codeTranslation_action
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) (v : U) :
    coreRepresentation (Fin 8) (codeTranslation U hd hone hw φ hφ) v.val =
      v.val + φ v • oneWord := by
  have hinv : (codeTranslation U hd hone hw φ hφ)⁻¹ = codeTranslation U hd hone hw φ hφ :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using codeTranslation_sq U hd hone hw φ hφ)
  apply Subtype.ext
  funext i
  change v.val.val ((codeTranslation U hd hone hw φ hφ)⁻¹ i) = v.val.val i + φ v * 1
  rw [hinv,codeTranslation_coordinate,mul_one]

open Representation Representation.BinaryOffender in
theorem codeTranslation_mem_stabilizer
    (φ : Module.Dual (ZMod 2) U) (hφ : φ ⟨oneWord,hone⟩ = 0) :
    (⟨codeTranslation U hd hone hw φ hφ,codeTranslation_even U hd hone hw φ hφ⟩ :
      alternatingGroup (Fin 8)) ∈ subspaceStabilizer (alternatingCoreRepresentation (Fin 8)) U := by
  let t := codeTranslation U hd hone hw φ hφ
  have hp (v : core (Fin 8)) (hv : v ∈ U) : coreRepresentation (Fin 8) t v ∈ U := by
    rw [codeTranslation_action U hd hone hw φ hφ ⟨v,hv⟩]
    exact U.add_mem hv (U.smul_mem _ hone)
  intro v
  constructor
  · intro hv
    have hh := hp _ hv
    have ht : t * t = 1 := by simpa only [pow_two] using codeTranslation_sq U hd hone hw φ hφ
    change coreRepresentation (Fin 8) t (coreRepresentation (Fin 8) t v) ∈ U at hh
    simpa only [← Module.End.mul_apply,←map_mul,ht,map_one,Module.End.one_apply] using hh
  · exact hp v

end BinaryPermutation.EightCore
