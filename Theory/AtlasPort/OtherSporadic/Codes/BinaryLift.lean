/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.Parity
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
The binary Golay encoder on six tetrads, with its even subcode and twist.
Explicit block decoding and parity identities connect this construction to
the six-coordinate hexacode.

Source: `Atlas/Codes/BinaryLift.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0: public module imports and exposed definition bodies
preserve downstream coordinate reductions; proof syntax and simplifier arguments
are adjusted for this toolchain. The mathematical declarations are unchanged.
-/

@[expose] public section

namespace Atlas.Codes
open scoped BigOperators
abbrev Tetrad := Fin 4
abbrev Omega := HexIndex × Tetrad
abbrev BinaryWord := Omega → Bit

def hexIndexEquiv : HexIndex ≃ Fin 6 := finProdFinEquiv

def binaryDot {ι : Type*} [Fintype ι] : LinearMap.BilinForm Bit (ι → Bit) :=
  dotProductBilin Bit Bit
theorem binaryDot_apply {ι : Type*} [Fintype ι] (u v : ι → Bit) :
    binaryDot u v = ∑ i, u i * v i := rfl

theorem binaryDot_symmetric {ι : Type*} [Fintype ι] (u v : ι → Bit) :
    binaryDot u v = binaryDot v u := by simp [binaryDot_apply, mul_comm]

theorem binaryDot_nondegenerate {ι : Type*} [Fintype ι] :
    (binaryDot (ι := ι)).Nondegenerate := by
  classical
  have hl : ∀ u : ι → Bit, (∀ v, binaryDot u v = 0) → u = 0 := by
    intro u hu
    funext i
    simpa [binaryDot, dotProductBilin, dotProduct, Pi.single_apply, mul_ite] using hu (Pi.single i 1)
  exact ⟨hl, fun u hu => hl u (fun v => by rw [binaryDot_symmetric]; exact hu v)⟩

def j : K →ₗ[Bit] (Tetrad → Bit) where
  toFun u := ![0, u.2, u.1, u.1 + u.2]
  map_add' := by intros; ext i; fin_cases i <;> simp; ring
  map_smul' := by intros; ext i; fin_cases i <;> simp [mul_add]

def blockDecode : (Tetrad → Bit) →ₗ[Bit] K where
  toFun w := (w 2 + w 0, w 1 + w 0)
  map_add' := by intros; ext <;> simp <;> ring
  map_smul' := by intros; ext <;> simp [mul_add]

theorem j_table : j 0 = ![0,0,0,0] ∧ j a = ![0,0,1,1] ∧
    j b = ![0,1,0,1] ∧ j c = ![0,1,1,0] := by decide
@[simp] theorem j_first (u : K) : j u 0 = 0 := rfl
@[simp] theorem j_sum : ∀ u, ∑ i, j u i = 0 := by decide
@[simp] theorem j_dot : ∀ u v, binaryDot (j u) (j v) = polar u v := by decide
@[simp] theorem j_dot_ones : ∀ u, binaryDot (j u) (fun _ => 1) = 0 := by decide
@[simp] theorem j_dot_first : ∀ u, binaryDot (j u) ![1,0,0,0] = 0 := by decide
@[simp] theorem blockDecode_j : ∀ u, blockDecode (j u) = u := by decide
@[simp] theorem blockDecode_constant : ∀ r : Bit, blockDecode (fun _ => r) = 0 := by decide

theorem j_injective : Function.Injective j := Function.LeftInverse.injective blockDecode_j

def jWord : HexWord →ₗ[Bit] BinaryWord where
  toFun w p := j (w p.1) p.2
  map_add' := by intros; funext p; exact congrFun (j.map_add _ _) p.2
  map_smul' := by intros; funext p; exact congrFun (j.map_smul _ _) p.2

def rho : (Fin 6 → Bit) →ₗ[Bit] BinaryWord where
  toFun r p := r (hexIndexEquiv p.1)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def eta : BinaryWord := fun p =>
  if p.1 = (2, 1) then ![0,1,1,1] p.2 else ![1,0,0,0] p.2

theorem eta_weight : hammingNorm eta = 8 := by decide
@[simp] theorem eta_block_sum : ∀ i : HexIndex, ∑ k, eta (i, k) = 1 := by decide
@[simp] theorem eta_block_dot_j : ∀ (i : HexIndex) (u : K),
    binaryDot (fun k => eta (i, k)) (j u) = 0 := by decide

def R0 : Submodule Bit BinaryWord := P6.map rho

def c0Encoder : (hexacode × P6) →ₗ[Bit] BinaryWord where
  toFun t := jWord t.1.val + rho t.2.val
  map_add' := by intros; simp; abel
  map_smul' := by intros; simp [smul_add]

def C0 : Submodule Bit BinaryWord := c0Encoder.range

def golayEncoder : (hexacode × P6 × Bit) →ₗ[Bit] BinaryWord where
  toFun t := c0Encoder (t.1, t.2.1) + t.2.2 • eta
  map_add' := by intros; simp [c0Encoder, add_smul]; abel
  map_smul' := by intros; simp [c0Encoder, smul_add, mul_smul]

def golay : Submodule Bit BinaryWord := golayEncoder.range

def blockParity (w : BinaryWord) (i : HexIndex) : Bit := ∑ k, w (i, k)

theorem golayEncoder_blockParity (h : hexacode) (r : P6) (ε : Bit) (i : HexIndex) :
    blockParity (golayEncoder (h, r, ε)) i = ε := by
  simp [blockParity, golayEncoder, c0Encoder, jWord, rho,
    Finset.sum_add_distrib, ← Finset.mul_sum, Fintype.card_fin, nsmul_eq_mul]

end Atlas.Codes
