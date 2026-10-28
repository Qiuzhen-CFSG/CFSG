module
public import Theory.Representation.IsotypicTwisted
public import Theory.Representation.Suzuki.SteinbergMultiplicity
public import Theory.Representation.Suzuki.SteinbergRegularActors
/-!
# Twisted regular coordinates on the actual Suzuki Steinberg isotypic part

The canonical isotypic component has finite Steinberg-copy coordinates.
An actor inducing the specified inner root action gives a constructed
multiplicity representation and literal twisted regular coordinates.
This theorem works with the original actor type, including quotient actors.

Source: Aschbacher–Smith §13.6, printed p.935.
-/

public noncomputable section
open scoped MonoidAlgebra
open Representation Module
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- Construct the full multiplicity action on the canonical Steinberg part. -/
theorem steinberg_isotypic_twisted_coordinates
    (m : ℕ) (hm : 1 ≤ m) {K A V : Type*} [Field K] [Algebra (F m) K] [Group A]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (SuzukiMatrixGroup m) V)
    (τ : Representation K A V) (φ : A →* SuzukiRootSubgroup m)
    (hc : ∀ a d, τ a * ρ d =
      ρ ((φ a : SuzukiMatrixGroup m) * d * (φ a : SuzukiMatrixGroup m)⁻¹) * τ a) :
    let S := Subrepresentation.ofSubmodule' (isotypicComponent K[SuzukiMatrixGroup m]
      ρ.asModule (tensorRep m K Finset.univ).asModule)
    ∃ (n : ℕ) (τS : Representation K A S.toSubmodule)
      (c : S.toSubmodule ≃ₗ[K] (SuzukiRootSubgroup m → Fin n → K))
      (μ : Representation K A (Fin n → K)),
      (∀ a v, (τS a v : V) = τ a v) ∧
      ∀ a v x, c (τS a v) x = μ a (c v ((φ a)⁻¹*x)) := by
  classical
  let : Fintype (SuzukiRootSubgroup m) := Fintype.ofFinite _
  let : IsIrreducible (tensorRep m K Finset.univ) := tensorRep_irreducible hm _
  let : IsAbsolutelyIrreducible (tensorRep m K Finset.univ) :=
    tensorRep_absolutelyIrreducible m hm K _
  obtain ⟨e,he⟩ := full_tensor_regular_coordinates m hm K
  exact SchurCopies.isotypic_twisted_coordinates ρ (tensorRep m K Finset.univ)
    τ φ (SuzukiRootSubgroup m).subtype hc e he
end Representation.SuzukiSmallDegree
