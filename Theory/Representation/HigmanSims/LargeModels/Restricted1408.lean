module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Matrices
public import Theory.Representation.HigmanSims.LargeModels.ScalarExtension

/-!
# Assembly from the degree-1408 restriction certificates

A marked action on the literal HS carrier and density of its two generating
matrices imply absolute irreducibility. Transport the matrix algebra to the
endomorphism algebra, then use the scalar-extension density theorem. The
existing scalar-extension interface gives the model over every field of
characteristic two.

The matrix descent and density certificates remain explicit. This module does
not yet assert `restrictedModelExists`. Both certificates must be supplied
before it can discharge the degree-1408 input to the seven-model assembly.
Candidate provenance: ATLAS HSd2G1-f2r1408B0 and HSd2G1-max1W1, recorded in
`Restricted1408/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels

open Sporadic.LeechRelated.HS

namespace Restricted1408

/-- Density of the two marked matrices proves absolute irreducibility of
the action of the literal permutation carrier. -/
theorem absolutelyIrreducible_of_matrices
    (a b : Mat) (ρ : Representation (ZMod 2) Carrier Vector)
    (ha : LinearMap.toMatrix' (ρ generatorAElement) = a)
    (hb : LinearMap.toMatrix' (ρ generatorBElement) = b)
    (hd : Algebra.adjoin (ZMod 2) {a, b} = ⊤) : ρ.IsAbsolutelyIrreducible := by
  let P := Algebra.adjoin (ZMod 2) (Set.range ρ)
  let e : Module.End (ZMod 2) Vector ≃ₐ[ZMod 2] Mat := LinearMap.toMatrixAlgEquiv'
  let Q := P.map e.toAlgHom
  have hqa : a ∈ Q := by
    rw [← ha]
    exact ⟨ρ generatorAElement, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hqb : b ∈ Q := by
    rw [← hb]
    exact ⟨ρ generatorBElement, Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  have hQ : Q = ⊤ := by
    apply top_unique
    rw [← hd]
    apply Algebra.adjoin_le
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact hqa
    · rw [Set.mem_singleton_iff.mp hx]
      exact hqb
  have hP : P = ⊤ := by
    apply top_unique
    intro f _
    have hf : e f ∈ Q := by rw [hQ]; trivial
    obtain ⟨f', hf', he⟩ := hf
    exact e.injective he ▸ hf'
  refine ⟨?_⟩
  apply irreducible_of_jacobson_density_surjective
  exact (extendScalars_surj_iff (AlgebraicClosure (ZMod 2)) ρ).mp hP

end Restricted1408

open Restricted1408

/-- The two concrete certificates supply precisely the binary model contract;
neither certificate assumes absolute irreducibility of the desired action. -/
theorem restrictedModelExists_of_descent_and_density
    (hm : MatrixDescentExists) (hd : MatrixAlgebraIsFull) : RestrictedModelExists := by
  intro hs
  obtain ⟨ρ, ha, hb⟩ := hm hs
  exact ⟨ρ, absolutelyIrreducible_of_matrices matrixA matrixB ρ ha hb hd⟩

/-- Application of the existing scalar-extension consumer to the action
assembled from the literal restricted matrices. -/
theorem restrictedModel_over_field_of_descent_and_density
    (hm : MatrixDescentExists) (hd : MatrixAlgebraIsFull) (hs : IsSimpleGroup Carrier)
    (F : Type*) [Field F] [CharP F 2] :
    ∃ ρ : Representation F Carrier (Fin 1408 → F), ρ.IsIrreducible :=
  restrictedModel_over_field (restrictedModelExists_of_descent_and_density hm hd) hs F

end Representation.HigmanSims.LargeModels
