/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.GolayRecovery
public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineRows

/-!
# EvenBlockGeometry

The even binary four-block splits into a Kleinian letter and a constant bit. The
explicit linear equivalence identifies the quotient by constants and relates binary
weight and dot product to the Kleinian quadratic and polar forms.

Source: `Atlas/Codes/EvenBlockGeometry.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

/-- Every even tetrad is uniquely a Kleinian letter plus a constant block. -/
def evenBlockEquiv : E4 ≃ₗ[Bit] (K × Bit) where
  toFun w := (blockDecode w.val,w.val 0)
  invFun t := ⟨j t.1 + fun _ => t.2,(parityCode_mem 3 _).mpr (by simp [Finset.sum_add_distrib])⟩
  left_inv w := Subtype.ext (even_block_decomposition w.val ((parityCode_mem 3 _).mp w.prop)).symm
  right_inv t := by
    apply Prod.ext
    · simp
    · change j t.1 0 + t.2 = t.2
      simp
  map_add' := by intros; apply Prod.ext <;> simp
  map_smul' := by intros; apply Prod.ext <;> simp

def evenBlockProjection : E4 →ₗ[Bit] K :=
  (LinearMap.fst Bit K Bit).comp evenBlockEquiv.toLinearMap

def constantEvenBlock : Bit →ₗ[Bit] E4 where
  toFun r := ⟨fun _ => r,(parityCode_mem 3 _).mpr (by simp)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem evenBlockProjection_surjective : Function.Surjective evenBlockProjection := by
  intro u
  exact ⟨evenBlockEquiv.symm (u,0),congrArg Prod.fst (evenBlockEquiv.apply_symm_apply (u,0))⟩

theorem evenBlockProjection_kernel : evenBlockProjection.ker = constantEvenBlock.range := by
  ext w
  constructor
  · intro hw
    refine ⟨w.val 0,?_⟩
    apply Subtype.ext
    have he := even_block_decomposition w.val ((parityCode_mem 3 _).mp w.prop)
    change blockDecode w.val = 0 at hw
    rw [hw,map_zero,zero_add] at he
    exact he.symm
  · rintro ⟨r,rfl⟩
    exact blockDecode_constant r

noncomputable def evenBlockQuotientEquiv :
    (E4 ⧸ evenBlockProjection.ker) ≃ₗ[Bit] K :=
  evenBlockProjection.quotKerEquivOfSurjective evenBlockProjection_surjective

/-- The half-weight quadratic form is exactly the anisotropic Kleinian form. -/
theorem evenBlock_half_weight : ∀ w : Fin 4 → Bit, (∑ k, w k = 0) →
    ((hammingNorm w / 2 : ℕ) : Bit) = qK (blockDecode w) := by decide

theorem evenBlock_polar : ∀ w z : Fin 4 → Bit, (∑ k, w k = 0) → (∑ k, z k = 0) →
    binaryDot w z = polar (blockDecode w) (blockDecode z) := by decide

end Atlas.Codes
