/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TetradGluingNormalization

/-!
# TetradMonomialLift

A monomial equivalence of recovered hexacodes lifts to an equivalence of the binary
tetrad codes. After normalizing the gluing and odd extension, the affine coordinate
permutation identifies the code with Golay.

Source: `Atlas/Codes/TetradMonomialLift.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

theorem monomialMarkedCode_lift (D : Submodule Bit HexWord) (g : Monomial HexIndex)
    (hg : ∀ h, h ∈ D ↔ Monomial.act g h ∈ hexacode)
    (h : D) (r : P6) (ε : Bit) :
    coordinatePermutation (affinePermutation 0 g) (jWord h.val+rho r.val+ε • eta) ∈ golay := by
  rw [← rowEncoder_lift,affine_encoder_transform]
  apply (rowEncoder_mem_iff _ _ _).mpr
  constructor
  · simpa using (hg h.val).mp h.prop
  · rw [affineRepetition_sum,Equiv.sum_comp hexIndexEquiv]
    have hr := (parityCode_mem 5 r.val).mp r.prop
    simp [hr,wordQ,qK]

theorem permutedBinaryCode_finrank (E : Submodule Bit BinaryWord) (σ : Equiv.Perm Omega) :
    Module.finrank Bit (permutedBinaryCode E σ) = Module.finrank Bit E := by
  exact ((coordinatePermutation σ).submoduleMap E).finrank_eq.symm

/-- The whole code, after arbitrary tetrad coordinates, is equivalent to the retained Golay code. -/
theorem tetradCode_equivalent (E : Submodule Bit BinaryWord) (hE : IsTetradCode E) :
    ∃ (t : HexWord) (g : Monomial HexIndex), ∀ w : BinaryWord,
      w ∈ E ↔ coordinatePermutation (affinePermutation 0 g * affinePermutation t 1) w ∈ golay := by
  obtain ⟨t,ht⟩ := tetradCode_normalized E hE
  obtain ⟨g,hg⟩ := tetradHexacode_unique E hE
  let σ := affinePermutation 0 g * affinePermutation t 1
  have hle : permutedBinaryCode E σ ≤ golay := by
    rintro _ ⟨w,hw,rfl⟩
    have hv := (permutedBinaryCode_mem E (affinePermutation t 1) w).mpr hw
    obtain ⟨h,r,ε,he⟩ := (ht _).mp hv
    change coordinatePermutation σ w ∈ golay
    rw [coordinatePermutation_mul,he]
    exact monomialMarkedCode_lift _ g hg h r ε
  have heq : permutedBinaryCode E σ = golay := Submodule.eq_of_le_of_finrank_eq hle (by
    rw [permutedBinaryCode_finrank,tetradCode_finrank E hE,golay_finrank])
  refine ⟨t,g,?_⟩
  intro w
  exact ((permutedBinaryCode_mem E σ w).symm).trans (by rw [heq])

end Atlas.Codes
