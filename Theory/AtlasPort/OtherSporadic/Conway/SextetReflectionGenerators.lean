/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/SextetReflectionGenerators.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.SextetReflection
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechGeneratorCriterion
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/SextetReflectionGenerators.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def reflectionOrigin : Omega := ((2,1),0)
abbrev ReflectionGeneratorIndex := Omega ⊕ (Fin 12 ⊕ Bool)

def reflectionGenerator : ReflectionGeneratorIndex → IntegerCoordinates
  | .inl i => coordinateVector i 4 - coordinateVector reflectionOrigin 4
  | .inr (.inl j) => (2 : ℤ) • golayIntegerLift (golayGenerators j)
  | .inr (.inr false) => coordinateVector reflectionOrigin 8
  | .inr (.inr true) => oddGlue reflectionOrigin

def sextetReflectionInteger (x : IntegerCoordinates) : IntegerCoordinates :=
  fun p => (if p.1 = (2,1) then -1 else 1) *
    (x p - (∑ k : Tetrad, x (p.1,k)) / 2)

def reflectionGeneratorImage (i : ReflectionGeneratorIndex) : IntegerCoordinates :=
  sextetReflectionInteger (reflectionGenerator i)

def reflectionGeneratorParity : ReflectionGeneratorIndex → ℤ
  | .inr (.inl 11) => 1
  | .inr (.inr true) => 1
  | _ => 0

theorem golay_mem_of_basis_orthogonal (c : BinaryWord)
    (h : ∀ i : Fin 12, binaryDot (golayGenerators i) c = 0) : c ∈ golay := by
  rw [golay_selfDual]
  intro x hx
  have hs := congrArg Subtype.val (golayBasis.sum_repr (⟨x,hx⟩ : golay))
  change (∑ i, golayBasis.repr ⟨x,hx⟩ i • (golayBasis i).val) = x at hs
  rw [← hs]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,golayBasis_coe,h,smul_zero,Finset.sum_const_zero]

/-- Small checks on the prescribed 38 gluing generators, all reduced by the kernel. -/
theorem reflection_generators_rational : ∀ i : ReflectionGeneratorIndex,
    sextetReflection (rationalEmbedding (reflectionGenerator i)) =
      rationalEmbedding (reflectionGeneratorImage i) := by decide +kernel

theorem reflection_generators_parity : ∀ i : ReflectionGeneratorIndex,
    (reflectionGeneratorParity i = 0 ∨ reflectionGeneratorParity i = 1) ∧
    (∀ p : Omega, reflectionGeneratorImage i p % 2 = reflectionGeneratorParity i) ∧
    (∑ p : Omega, reflectionGeneratorImage i p) % 8 = 4 * reflectionGeneratorParity i := by decide

theorem reflection_generators_code : ∀ i : ReflectionGeneratorIndex, ∀ j : Fin 12,
    binaryDot (golayGenerators j)
      (halfResidue (reflectionGeneratorImage i) (reflectionGeneratorParity i)) = 0 := by decide

theorem reflectionGeneratorImage_mem (i : ReflectionGeneratorIndex) :
    reflectionGeneratorImage i ∈ leech := by
  apply (mem_leech _).mpr
  exact ⟨reflectionGeneratorParity i,(reflection_generators_parity i).1,
    (reflection_generators_parity i).2.1,
    golay_mem_of_basis_orthogonal _ (reflection_generators_code i),
    (reflection_generators_parity i).2.2⟩

theorem sextetReflection_lattice (x : IntegerCoordinates) (hx : x ∈ leech) :
    sextetReflection (rationalEmbedding x) ∈ rationalLeech := by
  let P : Submodule ℤ IntegerCoordinates := rationalLeech.comap
    ((sextetReflection.restrictScalars ℤ).comp rationalEmbedding)
  have hp (i : ReflectionGeneratorIndex) : reflectionGenerator i ∈ P := by
    change sextetReflection (rationalEmbedding (reflectionGenerator i)) ∈ rationalLeech
    rw [reflection_generators_rational]
    exact ⟨reflectionGeneratorImage i,reflectionGeneratorImage_mem i,rfl⟩
  exact leech_le_of_generators P reflectionOrigin
    (fun i => hp (.inl i)) (hp (.inr (.inr false)))
    (fun j => hp (.inr (.inl j))) (hp (.inr (.inr true))) hx

end Atlas.Conway
