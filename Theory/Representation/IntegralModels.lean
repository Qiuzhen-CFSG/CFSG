module

public import Theory.LinearAlgebra.FractionLatticeBasis
public import Theory.Representation.InvariantIntegralSpan
public import Theory.Representation.CoefficientReduction
public import Mathlib.LinearAlgebra.Trace

/-!
# Integral models over a principal ideal domain

A finite-dimensional representation of a finite monoid over the fraction
field of a PID admits an integral matrix model of the same dimension. Take
the integral span of the translates of a field basis. It is finite free;
its integral basis remains a field basis by clearing denominators. The
matrices in these two bases agree under the coefficient embedding, so their
traces agree as well.

This is the invariant-lattice argument of Serre, *Linear Representations of
Finite Groups*, Chapter 15. Existence of a model over a particular fraction
field is a separate field-of-definition question.
-/

public section

noncomputable section
namespace Representation
variable (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {K G V : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [Monoid G] [Finite G] [AddCommGroup V] [Module K V] [Module R V]
  [IsScalarTower R K V] [FiniteDimensional K V]

/-- An integral model whose coefficient extension has the original action matrices. -/
theorem exists_integral_model (ρ : Representation K G V) :
    ∃ (m : ℕ) (σ : Representation R G (Fin m → R)) (b : Module.Basis (Fin m) K V),
      ∀ g, LinearMap.toMatrix b b (ρ g) =
        LinearMap.toMatrix' (mapCoefficients (algebraMap R K) σ g) := by
  classical
  let L := orbitSpan R ρ (Module.finBasis K V)
  let b := Module.finBasis R L
  have hL : Submodule.span K (L : Set V) = ⊤ :=
    span_orbitSpan_eq_top R ρ _ (Module.finBasis K V).span_eq
  let bK := L.fractionBasis b hL
  let τ := orbitSpanRepresentation R ρ (Module.finBasis K V)
  let σ : Representation R G (Fin (Module.finrank R L) → R) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp τ)
  refine ⟨Module.finrank R L, σ, bK, ?_⟩
  intro g
  rw [mapCoefficients_toMatrix]
  have hσ : LinearMap.toMatrix' (σ g) = LinearMap.toMatrix b b (τ g) :=
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
  rw [hσ]
  ext i j
  simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
  change bK.repr (ρ g (bK j)) i = algebraMap R K (b.repr (τ g (b j)) i)
  rw [show bK j = (b j : V) from L.fractionBasis_apply b hL j]
  exact L.fractionBasis_repr b hL (τ g (b j)) i

/-- The integral model has the original rank and character over the fraction field. -/
theorem exists_integral_model_trace (ρ : Representation K G V) :
    ∃ (m : ℕ) (σ : Representation R G (Fin m → R)),
      m = Module.finrank K V ∧ ∀ g,
        LinearMap.trace K _ (mapCoefficients (algebraMap R K) σ g) =
          LinearMap.trace K V (ρ g) := by
  obtain ⟨m, σ, b, hb⟩ := exists_integral_model R ρ
  refine ⟨m, σ, ?_, ?_⟩
  · simpa using (Module.finrank_eq_card_basis b).symm
  · intro g
    rw [LinearMap.trace_eq_matrix_trace K b,
      LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin m))]
    exact congrArg Matrix.trace (hb g).symm
end Representation
