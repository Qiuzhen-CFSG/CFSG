module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.BinaryModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees120252.Data

/-!
# Native realization and density for the two candidate pairs

A realization is a lawful representation of the actual Witt-design M24 with
the two specified generator matrices. It contains no irreducibility assertion.
If these matrices generate the full matrix algebra, the actual representation
generates every endomorphism. Scalar extension preserves this equality and
Jacobson density proves absolute irreducibility.

The native realization is a separate construction obligation: matrix relations
or an ATLAS group label do not furnish it. This reduction is used by the
degree-120/252 assembly for James's binary modules (J. Algebra 27 (1973),
57–111), as consumed in Guralnick–Malle I, Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
namespace Degrees120252
open Sporadic.Mathieu

/-- The literal native standard generators, in the order of the matrix files. -/
def actor : Fin 2 → M24 :=
  ![⟨m24GeneratorA, m24GeneratorA_mem⟩, ⟨m24GeneratorB, m24GeneratorB_mem⟩]

/-- A comparison with the native carrier; no simplicity or spectrum premise. -/
structure NativeRealization (d : ℕ)
    (A : Fin 2 → Matrix (Fin d) (Fin d) (ZMod 2)) where
  representation : Representation (ZMod 2) M24 (Fin d → ZMod 2)
  matrix_actor : ∀ j, LinearMap.toMatrix' (representation (actor j)) = A j

/-- Density of the candidate matrices gives density of the actual group action.
The two actors need not generate M24 for this implication. -/
theorem NativeRealization.density {d : ℕ}
    {A : Fin 2 → Matrix (Fin d) (Fin d) (ZMod 2)}
    (r : NativeRealization d A)
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
      (∀ j, A j ∈ Q) → Q = ⊤) :
    Algebra.adjoin (ZMod 2) (Set.range r.representation) = ⊤ := by
  let P := Algebra.adjoin (ZMod 2) (Set.range r.representation)
  let e : Module.End (ZMod 2) (Fin d → ZMod 2) ≃ₐ[ZMod 2]
      Matrix (Fin d) (Fin d) (ZMod 2) := LinearMap.toMatrixAlgEquiv'
  let Q := P.map e.toAlgHom
  have hQ : Q = ⊤ := hA Q fun j => by
    rw [← r.matrix_actor j]
    exact ⟨r.representation (actor j),
      Algebra.subset_adjoin (Set.mem_range_self _), rfl⟩
  apply top_unique
  intro f _
  have hf : e f ∈ Q := by rw [hQ]; trivial
  obtain ⟨f', hf', he⟩ := hf
  exact e.injective he ▸ hf'

/-- The actual action is absolutely irreducible once its matrices are dense. -/
theorem NativeRealization.absolute {d : ℕ} [NeZero d]
    {A : Fin 2 → Matrix (Fin d) (Fin d) (ZMod 2)}
    (r : NativeRealization d A)
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
      (∀ j, A j ∈ Q) → Q = ⊤) : r.representation.IsAbsolutelyIrreducible := by
  refine ⟨?_⟩
  apply irreducible_of_jacobson_density_surjective
  exact (extendScalars_surj_iff (AlgebraicClosure (ZMod 2)) r.representation).mp
    (r.density hA)

/-- A native realization and an independently checked algebra certificate
give the exact model type consumed by the larger-spectrum assembly. -/
def NativeRealization.binaryModel {d : ℕ} [NeZero d]
    {A : Fin 2 → Matrix (Fin d) (Fin d) (ZMod 2)}
    (r : NativeRealization d A)
    (hA : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin d) (Fin d) (ZMod 2)),
      (∀ j, A j ∈ Q) → Q = ⊤) : BinaryModel d :=
  ⟨r.representation, r.absolute hA⟩

end Degrees120252
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels
