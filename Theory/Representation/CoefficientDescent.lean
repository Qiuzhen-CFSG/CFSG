module

public import Theory.Representation.CoefficientReduction

/-!
# Descent of action matrices

A representation descends along an injective coefficient map when the entries
of its action matrices lie in the image. Choose preimages of the entries;
injectivity then descends the identity and multiplication laws. A finite basis
version gives a model on a standard coordinate space with the same trace.

This is elementary matrix descent, used for the monomial representations in
the cyclotomic field-of-definition argument of Serre, *Linear Representations
of Finite Groups*, Chapter 12.
-/

public section

noncomputable section
namespace Representation
variable {R S G ι : Type*} [CommRing R] [CommRing S] [Monoid G]
  [Fintype ι] [DecidableEq ι]

/-- Lift a matrix representation when every matrix entry lifts. -/
theorem exists_mapCoefficients_eq_of_entries
    (f : R →+* S) (hf : Function.Injective f)
    (ρ : Representation S G (ι → S))
    (hρ : ∀ g i j, ∃ r, f r = LinearMap.toMatrix' (ρ g) i j) :
    ∃ σ : Representation R G (ι → R), mapCoefficients f σ = ρ := by
  classical
  choose A₀ hA using hρ
  let A : G → Matrix ι ι R := fun g => Matrix.of (A₀ g)
  have hm (g : G) : f.mapMatrix (A g) = LinearMap.toMatrixAlgEquiv' (ρ g) := by
    ext i j
    exact hA g i j
  have hi : Function.Injective (f.mapMatrix : Matrix ι ι R → Matrix ι ι S) := by
    intro a b h
    ext i j
    exact hf (congrFun (congrFun h i) j)
  let a : G →* Matrix ι ι R :=
    { toFun := A
      map_one' := by
        apply hi
        rw [hm, map_one, map_one, map_one]
      map_mul' := by
        intro g h
        apply hi
        rw [map_mul, hm, hm, hm, map_mul, map_mul] }
  refine ⟨Matrix.toLinAlgEquiv'.toMonoidHom.comp a, ?_⟩
  apply MonoidHom.ext
  intro g
  apply LinearMap.toMatrix'.injective
  rw [mapCoefficients_toMatrix]
  change (LinearMap.toMatrixAlgEquiv' (Matrix.toLinAlgEquiv' (A g))).map f = _
  rw [LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv']
  exact hm g
end Representation

namespace Representation
variable {R S G ι V : Type*} [CommRing R] [CommRing S] [Monoid G]
  [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module S V]

/-- Descend in a finite basis and use standard finite coordinates. -/
theorem exists_model_of_basis_entries
    (f : R →+* S) (hf : Function.Injective f)
    (ρ : Representation S G V) (b : Module.Basis ι S V)
    (hρ : ∀ g i j, ∃ r, f r = LinearMap.toMatrix b b (ρ g) i j) :
    ∃ σ : Representation R G (Fin (Fintype.card ι) → R), ∀ g,
      LinearMap.trace S _ (mapCoefficients f σ g) = LinearMap.trace S V (ρ g) := by
  classical
  let b' := b.reindex (Fintype.equivFin ι)
  let τ : Representation S G (Fin (Fintype.card ι) → S) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp ((LinearMap.toMatrixAlgEquiv b').toMonoidHom.comp ρ)
  have hτ (g : G) : LinearMap.toMatrix' (τ g) = LinearMap.toMatrix b' b' (ρ g) :=
    LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
  obtain ⟨σ, hσ⟩ := exists_mapCoefficients_eq_of_entries f hf τ (by
    intro g i j
    rw [hτ]
    simpa only [LinearMap.toMatrix_apply, b', Module.Basis.reindex_apply,
      Module.Basis.repr_reindex_apply] using
      hρ g ((Fintype.equivFin ι).symm i) ((Fintype.equivFin ι).symm j))
  refine ⟨σ, fun g => ?_⟩
  rw [hσ, LinearMap.trace_eq_matrix_trace S b',
    LinearMap.trace_eq_matrix_trace S (Pi.basisFun S (Fin (Fintype.card ι)))]
  exact congrArg Matrix.trace (hτ g)
end Representation
