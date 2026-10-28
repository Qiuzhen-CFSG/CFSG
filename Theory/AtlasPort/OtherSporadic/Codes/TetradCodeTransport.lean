/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradOddExtension
public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineCodeCriterion

/-!
# TetradCodeTransport

Coordinate permutations preserve the binary dot product and self-duality. Affine
monomial permutations preserve the even repetition subcode as well, allowing the
complete tetrad-code hypotheses to be transported.

Source: `Atlas/Codes/TetradCodeTransport.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def permutedBinaryCode (E : Submodule Bit BinaryWord) (σ : Equiv.Perm Omega) :
    Submodule Bit BinaryWord := E.map (coordinatePermutation σ).toLinearMap

theorem coordinatePermutation_dot (σ : Equiv.Perm Omega) (w z : BinaryWord) :
    binaryDot (coordinatePermutation σ w) (coordinatePermutation σ z) = binaryDot w z := by
  simp only [binaryDot_apply,coordinatePermutation,LinearEquiv.coe_mk]
  exact Equiv.sum_comp σ.symm (fun p => w p*z p)

theorem permutedBinaryCode_mem (E : Submodule Bit BinaryWord) (σ : Equiv.Perm Omega) (w : BinaryWord) :
    coordinatePermutation σ w ∈ permutedBinaryCode E σ ↔ w ∈ E := by
  constructor
  · rintro ⟨z,hz,he⟩
    exact (coordinatePermutation σ).injective he ▸ hz
  · intro hw; exact ⟨w,hw,rfl⟩

theorem permutedBinaryCode_selfDual (E : Submodule Bit BinaryWord) (hE : E = binaryDot.orthogonal E)
    (σ : Equiv.Perm Omega) :
    permutedBinaryCode E σ = binaryDot.orthogonal (permutedBinaryCode E σ) := by
  ext v
  obtain ⟨w,rfl⟩ := (coordinatePermutation σ).surjective v
  rw [permutedBinaryCode_mem]
  constructor
  · intro hw
    rintro _ ⟨z,hz,rfl⟩
    change binaryDot (coordinatePermutation σ z) (coordinatePermutation σ w) = 0
    rw [coordinatePermutation_dot]
    have ho : w ∈ binaryDot.orthogonal E := by rw [← hE]; exact hw
    exact ho z hz
  · intro hw
    rw [hE]
    intro z hz
    have he := hw (coordinatePermutation σ z) ((permutedBinaryCode_mem E σ z).mpr hz)
    rw [coordinatePermutation_dot] at he
    exact he

theorem affinePermutation_repetition (t : HexWord) (g : Monomial HexIndex) (r : Fin 6 → Bit) :
    coordinatePermutation (affinePermutation t g) (rho r) =
      rho (fun i => r (hexIndexEquiv (g.perm.symm (hexPos i)))) := by
  funext p
  simp [coordinatePermutation,rho,affinePermutation]

theorem affinePermutation_R0 (t : HexWord) (g : Monomial HexIndex) :
    R0 ≤ permutedBinaryCode R0 (affinePermutation t g) := by
  rintro w ⟨r,hr,rfl⟩
  let s : Fin 6 → Bit := fun i => r (hexIndexEquiv (g.perm (hexPos i)))
  have hs : s ∈ P6 := by
    apply (parityCode_mem 5 s).mpr
    change ∑ i, r (((hexIndexEquiv.symm.trans g.perm).trans hexIndexEquiv) i) = 0
    rw [Equiv.sum_comp]
    exact (parityCode_mem 5 r).mp hr
  refine ⟨rho s,⟨s,hs,rfl⟩,?_⟩
  rw [show (coordinatePermutation (affinePermutation t g)).toLinearMap (rho s) =
    coordinatePermutation (affinePermutation t g) (rho s) from rfl,affinePermutation_repetition]
  congr 1
  funext i
  simp [s]

theorem permutedTetradCode (E : Submodule Bit BinaryWord) (hE : IsTetradCode E)
    (t : HexWord) (g : Monomial HexIndex) :
    IsTetradCode (permutedBinaryCode E (affinePermutation t g)) where
  self_dual := permutedBinaryCode_selfDual E hE.self_dual _
  doubly_even := by
    rintro _ ⟨w,hw,rfl⟩
    exact (coordinatePermutation_weight _ w) ▸ hE.doubly_even w hw
  minimum := by
    rintro _ ⟨w,hw,rfl⟩ hn
    have hn' : w ≠ 0 := by intro hz; apply hn; rw [hz,map_zero]
    exact (coordinatePermutation_weight _ w) ▸ hE.minimum w hw hn'
  repetitions := (affinePermutation_R0 t g).trans (Submodule.map_mono hE.repetitions)

end Atlas.Codes
