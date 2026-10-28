/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechRank.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechDual
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient

/-!
Freeness, finite generation, rank twenty-four, and full rational span.
The lattice contains eight times every integer coordinate vector, giving both rank bounds.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

theorem eight_mul_mem (x : IntegerCoordinates) : (8 : ℤ) • x ∈ leech := by
  apply Or.inl
  apply (mem_evenGolayLattice _).mpr
  refine ⟨(4 : ℤ) • x,?_,?_,?_⟩
  · have h : integerReduction ((4 : ℤ) • x) = 0 := by
      ext i
      change ((4 * x i : ℤ) : Bit) = 0
      simp
    rw [h]; exact golay.zero_mem
  · change (∑ i, 4 * x i) % 4 = 0
    rw [← Finset.mul_sum]
    omega
  · intro i
    change 8 * x i = 2 * (4 * x i)
    ring

def eightIntoLeech : IntegerCoordinates →ₗ[ℤ] leech where
  toFun x := ⟨8 • x,eight_mul_mem x⟩
  map_add' x y := by apply Subtype.ext; exact smul_add 8 x y
  map_smul' r x := by apply Subtype.ext; exact smul_comm 8 r x

theorem eightIntoLeech_injective : Function.Injective eightIntoLeech := by
  intro x y h
  have h := congrArg Subtype.val h
  ext i
  have hi := congrFun h i
  change 8 * x i = 8 * y i at hi
  linarith

theorem leech_rank : Module.finrank ℤ leech = 24 := by
  have h₁ := LinearMap.finrank_le_finrank_of_injective leech.subtype_injective
  have h₂ := LinearMap.finrank_le_finrank_of_injective eightIntoLeech_injective
  have h : Module.finrank ℤ IntegerCoordinates = 24 := by
    simp [IntegerCoordinates,Omega,HexIndex]
  rw [h] at h₁ h₂
  omega

theorem leech_free : Module.Free ℤ leech := inferInstance

theorem leech_finitelyGenerated : Module.Finite ℤ leech := inferInstance

theorem rationalLeech_full_span : Submodule.span ℚ (rationalLeech : Set RationalCoordinates) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have he : x = ∑ i : Omega, (x i / 8) • rationalEmbedding (coordinateVector i 8) := by
    ext j
    simp [rationalEmbedding,coordinateVector,Pi.single_apply,smul_eq_mul,mul_ite]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact Submodule.mem_map.mpr ⟨coordinateVector i 8,coordinate_eight_mem i,rfl⟩

end Atlas.Lattices
