module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Model
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Independent finite certificates and their literal coset consumer

The flag certificate supplies invariant subspaces and coordinates on their
literal successive quotients. The independent algebra certificate proves that
the displayed diagonal block pairs generate every matrix endomorphism. The
density criterion makes each actual quotient irreducible, and its coordinate
isomorphism proves the required dimension. Finally the coset coordinate
certificate transports this filtration to the omega-eigenspace of the actual
left-coset module. None of these certificate existences is assumed as an axiom.

Source application: Aschbacher–Smith K.1.3, printed p.453 (PDF p.464).
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- An actual invariant flag with the specified matrices on the literal
successive quotients. This structure does not assume simplicity. -/
structure FlagCoordinates where
  stage : ℕ → Subrepresentation representation
  zero : stage 0 = ⊥
  last : stage 9 = ⊤
  mono : ∀ m, m < 9 → stage m ≤ stage (m + 1)
  coordinates (t : Factor) :
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[F]
      (Fin (degree t) → F)
  generator_coordinates : ∀ (t : Factor) (j : Fin 2) v,
    coordinates t
      ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation (FreeGroup.of j) v) =
    (factorMatrix t j).mulVec (coordinates t v)

/-- Concrete matrix-algebra spanning, independently checkable for each of
the nine displayed pairs. It asserts no representation catalogue. -/
def FactorSpanning : Prop :=
  ∀ (t : Factor) (Q : Subalgebra F (Matrix (Fin (degree t)) (Fin (degree t)) F)),
    (∀ j, factorMatrix t j ∈ Q) → Q = ⊤

/-- The actual quotient coordinate maps and matrix spanning imply a genuine
factor-degree filtration of the fixed word representation. -/
theorem wordFiltration_of_certificates (D : FlagCoordinates) (hspan : FactorSpanning) :
    FactorDegreeFiltration ({3, 9} : Set ℕ) representation := by
  apply filtration_of_flag ({3, 9} : Set ℕ) 9 D.stage D.zero D.last D.mono
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    exact irreducible_of_coordinate_matrices (degree_pos t) FreeGroup.of
      (factorMatrix t) (D.coordinates t) (D.generator_coordinates t) (hspan t)
  · intro m hm
    let t : Factor := ⟨m, hm⟩
    have he := (D.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank F
      ((D.stage (t.val + 1)).toSubmodule ⧸
        (within (D.stage t.val) (D.stage (t.val + 1))).toSubmodule) ∈ ({3, 9} : Set ℕ)
    rw [he]
    exact degree_allowed t

/-- All three independent certificates feed the literal universal coset
representation required by the degree-twelve exclusion. -/
theorem cosetFiltration_of_certificates (C : CosetCoordinates) (D : FlagCoordinates)
    (hspan : FactorSpanning) : CosetFiltration :=
  cosetFiltration_of_wordFiltration C (wordFiltration_of_certificates D hspan)

end Representation.Hexacode.TwelveDimensional.CosetCertificate
