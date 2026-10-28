module

public import Theory.Representation.ExtendScalars
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Descent from an embedding into a scalar extension

If an irreducible F-representation embeds F-linearly and equivariantly in
the scalar extension of another irreducible F-representation, the two
original representations are equivalent. No finite dimension or
semisimplicity of the extended representation is needed.

Choose an F-basis of the extension field and project onto its coefficients.
At least one coefficient of the embedding is nonzero. Coefficient projection
commutes with the original action, and Schur's lemma makes that coefficient
map an isomorphism.

This supplies the descent step when a six-dimensional F₄ constituent is
used to recognize a twelve-dimensional binary module. The J₂ application
is in `J2.G2FourModule.ConstituentDescent`; the classification producing
that constituent remains a separate mathematical obligation. The initial
coefficient argument was retained from `Scratch/J2BinaryTwelveRecognition`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Representation.ScalarConstituents

variable {F E G V U : Type*} [Field F] [Field E] [Algebra F E] [Group G]
  [AddCommGroup V] [Module F V] [AddCommGroup U] [Module F U]

private def coefficient (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (k : Module.Free.ChooseBasisIndex F E) : E ⊗[F] V →ₗ[F] V :=
  (Finsupp.lapply k).comp (TensorProduct.equivFinsuppOfBasisLeft b).toLinearMap

private theorem coefficient_action (ρ : Representation F G V)
    (b : Module.Basis (Module.Free.ChooseBasisIndex F E) F E)
    (k : Module.Free.ChooseBasisIndex F E) (g : G) (z : E ⊗[F] V) :
    coefficient b k (extendScalars E ρ g z) = ρ g (coefficient b k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e v =>
    simp [coefficient, extendScalars_apply, LinearMap.baseChange_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- A nonzero equivariant map into a scalar extension has a nonzero
coefficient intertwiner over the original field. -/
theorem exists_nonzero_coefficient (ρ : Representation F G V)
    (τ : Representation F G U) (i : U →ₗ[F] E ⊗[F] V) (hi : i ≠ 0)
    (hcomm : ∀ g u, i (τ g u) = extendScalars E ρ g (i u)) :
    ∃ f : τ.IntertwiningMap ρ, f ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis F E
  obtain ⟨u, hu⟩ : ∃ u, i u ≠ 0 := by
    contrapose! hi
    exact LinearMap.ext hi
  have hne : (TensorProduct.equivFinsuppOfBasisLeft b) (i u) ≠ 0 := by
    intro h
    exact hu ((TensorProduct.equivFinsuppOfBasisLeft b).injective (by simpa using h))
  obtain ⟨k, hk⟩ : ∃ k, (TensorProduct.equivFinsuppOfBasisLeft b) (i u) k ≠ 0 := by
    contrapose! hne
    ext k
    exact hne k
  let f : τ.IntertwiningMap ρ :=
    ⟨(coefficient b k).comp i, fun g => LinearMap.ext fun u => by
      change coefficient b k (i (τ g u)) = ρ g (coefficient b k (i u))
      rw [hcomm, coefficient_action]⟩
  refine ⟨f, ?_⟩
  intro h
  exact hk (congrArg (fun f : τ.IntertwiningMap ρ => f u) h)

/-- Schur's lemma descends a nonzero scalar-extension map between simple
representations to an equivalence over the original field. -/
theorem equiv_of_nonzero_scalar_map (ρ : Representation F G V) [IsIrreducible ρ]
    (τ : Representation F G U) [IsIrreducible τ]
    (i : U →ₗ[F] E ⊗[F] V) (hi : i ≠ 0)
    (hcomm : ∀ g u, i (τ g u) = extendScalars E ρ g (i u)) :
    Nonempty (RepEquiv τ ρ) := by
  obtain ⟨f, hf⟩ := exists_nonzero_coefficient ρ τ i hi hcomm
  exact ⟨RepEquiv.ofRepresentationEquiv (f.ofBijective
    ⟨(IsIrreducible.injective_or_eq_zero f).resolve_right hf,
      (IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩)⟩

/-- Every nonzero equivariant map into a scalar extension of a faithful
irreducible representation has a faithful source action. This lets a
constituent classification retain the original faithfulness hypothesis. -/
theorem faithful_of_nonzero_scalar_map (ρ : Representation F G V) [IsIrreducible ρ]
    (hρ : Function.Injective ρ) (τ : Representation F G U)
    (i : U →ₗ[F] E ⊗[F] V) (hi : i ≠ 0)
    (hcomm : ∀ g u, i (τ g u) = extendScalars E ρ g (i u)) :
    Function.Injective τ := by
  obtain ⟨f, hf⟩ := exists_nonzero_coefficient ρ τ i hi hcomm
  have hsurj := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  intro g h hgh
  apply hρ
  ext v
  obtain ⟨u, rfl⟩ := hsurj v
  calc
    ρ g (f u) = f (τ g u) := (LinearMap.congr_fun (f.isIntertwining' g) u).symm
    _ = f (τ h u) := by rw [hgh]
    _ = ρ h (f u) := LinearMap.congr_fun (f.isIntertwining' h) u

/-- In particular, an equivariant embedding into the scalar extension
identifies the two original irreducible representations. -/
theorem equiv_of_scalar_embedding (ρ : Representation F G V) [IsIrreducible ρ]
    (τ : Representation F G U) [IsIrreducible τ]
    (i : U →ₗ[F] E ⊗[F] V) (hi : Function.Injective i)
    (hcomm : ∀ g u, i (τ g u) = extendScalars E ρ g (i u)) :
    Nonempty (RepEquiv τ ρ) := by
  apply equiv_of_nonzero_scalar_map ρ τ i _ hcomm
  intro h
  let : Nontrivial U := Subrepresentation.irreducible_module_nontrivial τ
  obtain ⟨u, hu⟩ := exists_ne (0 : U)
  apply hu
  apply hi
  rw [h]
  rfl

end Representation.ScalarConstituents
