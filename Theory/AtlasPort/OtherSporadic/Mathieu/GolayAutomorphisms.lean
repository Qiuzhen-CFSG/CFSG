/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayMarkings

/-!
Coordinate automorphisms of the constructed Golay code and its octads agree.
Permutations preserve weights and supports, and octads span the code.
The resulting Mathieu code model acts faithfully on the original coordinates.

Source: `Atlas/Mathieu/GolayAutomorphisms.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
open Finset

def coordinatePermutation (σ : Equiv.Perm Omega) : BinaryWord ≃ₗ[Bit] BinaryWord where
  toFun w p := w (σ⁻¹ p)
  invFun w p := w (σ p)
  left_inv := by intro w; funext p; simp
  right_inv := by intro w; funext p; simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem coordinatePermutation_one (w : BinaryWord) : coordinatePermutation 1 w = w := rfl
@[simp] theorem coordinatePermutation_mul (σ τ : Equiv.Perm Omega) (w : BinaryWord) :
    coordinatePermutation (σ*τ) w = coordinatePermutation σ (coordinatePermutation τ w) := rfl

theorem coordinatePermutation_weight (σ : Equiv.Perm Omega) (w : BinaryWord) :
    hammingNorm (coordinatePermutation σ w) = hammingNorm w := hammingNorm_equiv σ.symm w

def permuteBlock (σ : Equiv.Perm Omega) (O : Finset Omega) : Finset Omega := O.image σ

@[simp] theorem permuteBlock_one (O : Finset Omega) : permuteBlock 1 O = O := by simp [permuteBlock]
@[simp] theorem permuteBlock_mul (σ τ : Equiv.Perm Omega) (O : Finset Omega) :
    permuteBlock (σ*τ) O = permuteBlock σ (permuteBlock τ O) := by
  simp only [permuteBlock, image_image]
  rfl

theorem coordinatePermutation_support (σ : Equiv.Perm Omega) (w : BinaryWord) :
    support (coordinatePermutation σ w) = permuteBlock σ (support w) := by
  ext p
  simp only [support, mem_filter, mem_univ, true_and, permuteBlock, mem_image]
  constructor
  · intro h
    exact ⟨σ⁻¹ p,h,by simp⟩
  · rintro ⟨q,hq,rfl⟩
    simpa [coordinatePermutation] using hq

def CodePreserving (σ : Equiv.Perm Omega) : Prop :=
  ∀ w : BinaryWord, w ∈ golay ↔ coordinatePermutation σ w ∈ golay

def OctadPreserving (σ : Equiv.Perm Omega) : Prop :=
  ∀ O : Finset Omega, O ∈ octads ↔ permuteBlock σ O ∈ octads

def codeAutomorphisms : Subgroup (Equiv.Perm Omega) where
  carrier := CodePreserving
  one_mem' := by intro w; simp
  mul_mem' := by
    intro σ τ hσ hτ w
    rw [coordinatePermutation_mul]
    exact (hτ w).trans (hσ _)
  inv_mem' := by
    intro σ hσ w
    have h := hσ (coordinatePermutation σ⁻¹ w)
    rw [← coordinatePermutation_mul, mul_inv_cancel, coordinatePermutation_one] at h
    exact h.symm

def octadAutomorphisms : Subgroup (Equiv.Perm Omega) where
  carrier := OctadPreserving
  one_mem' := by intro O; simp
  mul_mem' := by
    intro σ τ hσ hτ O
    rw [permuteBlock_mul]
    exact (hτ O).trans (hσ _)
  inv_mem' := by
    intro σ hσ O
    have h := hσ (permuteBlock σ⁻¹ O)
    rw [← permuteBlock_mul, mul_inv_cancel, permuteBlock_one] at h
    exact h.symm

theorem codePreserving_octad_forward (σ : Equiv.Perm Omega) (hσ : CodePreserving σ)
    (O : Finset Omega) (hO : O ∈ octads) : permuteBlock σ O ∈ octads := by
  obtain ⟨w,hw,rfl⟩ := (octads_mem O).mp hO
  apply (octads_mem _).mpr
  refine ⟨⟨coordinatePermutation σ w.val,(hσ w.val).mp w.prop⟩,?_,coordinatePermutation_support σ w.val⟩
  exact (coordinatePermutation_weight σ w.val).trans hw

theorem codePreserving_octadPreserving (σ : Equiv.Perm Omega) (hσ : CodePreserving σ) : OctadPreserving σ := by
  intro O
  constructor
  · exact codePreserving_octad_forward σ hσ O
  · intro hO
    have hi : CodePreserving σ⁻¹ := codeAutomorphisms.inv_mem hσ
    have h := codePreserving_octad_forward σ⁻¹ hi (permuteBlock σ O) hO
    simpa only [← permuteBlock_mul, inv_mul_cancel, permuteBlock_one] using h

theorem octadPreserving_code_forward (σ : Equiv.Perm Omega) (hσ : OctadPreserving σ)
    (w : BinaryWord) (hw : w ∈ golay) : coordinatePermutation σ w ∈ golay := by
  rw [← octads_span] at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    have hO : support w ∈ octads := (octads_mem _).mpr ⟨⟨w,hw.1⟩,hw.2,rfl⟩
    obtain ⟨v,hv,he⟩ := (octads_mem _).mp ((hσ _).mp hO)
    have he' : v.val = coordinatePermutation σ w := support_injective
      (he.trans (coordinatePermutation_support σ w).symm)
    rw [← he']
    exact v.prop
  | zero => simp
  | add x y hx hy ihx ihy => simpa using golay.add_mem ihx ihy
  | smul a x hx ih => simpa using golay.smul_mem a ih

theorem octadPreserving_codePreserving (σ : Equiv.Perm Omega) (hσ : OctadPreserving σ) : CodePreserving σ := by
  intro w
  constructor
  · exact octadPreserving_code_forward σ hσ w
  · intro hw
    have hi : OctadPreserving σ⁻¹ := octadAutomorphisms.inv_mem hσ
    have h := octadPreserving_code_forward σ⁻¹ hi (coordinatePermutation σ w) hw
    simpa only [← coordinatePermutation_mul, inv_mul_cancel, coordinatePermutation_one] using h

theorem codeAutomorphisms_eq_octadAutomorphisms : codeAutomorphisms = octadAutomorphisms := by
  ext σ
  exact ⟨codePreserving_octadPreserving σ,octadPreserving_codePreserving σ⟩

/-- The coordinate-permutation code model; no order or simplicity is asserted here. -/
abbrev Mathieu24CodeModel := codeAutomorphisms

theorem codeAutomorphisms_finite : Finite Mathieu24CodeModel := inferInstance

theorem codeAutomorphisms_faithful : FaithfulSMul Mathieu24CodeModel Omega := inferInstance

end Atlas.Codes
