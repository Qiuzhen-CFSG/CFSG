module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.Contracts
public import Mathlib.RepresentationTheory.Character

/-!
# The degree-320 trace comparison on the native carrier

An intertwining equivalence preserves trace at the particular native element
`(actorA * actorB)^5 * actorB`. The marked generator equations identify this
trace with the same literal word in the downloaded matrices. Thus a checked
numerical trace inequality distinguishes the two native representations.

The expected traces are 0 and 1. The numerical check is a separate obligation;
this module proves the carrier application, without assuming irreducibility
or an external ATLAS assertion of inequivalence.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
open Sporadic.Mathieu

/-- The finite trace test; it makes no assertion about native group actions. -/
def TraceSeparation : Prop :=
  Matrix.trace ((matrixA false * matrixB false) ^ 5 * matrixB false) ≠
    Matrix.trace ((matrixA true * matrixB true) ^ 5 * matrixB true)

theorem character_word_of_realizes (variant : Bool)
    (ρ : Representation (ZMod 2) M24 Space) (hρ : Realizes variant ρ) :
    ρ.character ((actorA * actorB) ^ 5 * actorB) =
      Matrix.trace ((matrixA variant * matrixB variant) ^ 5 * matrixB variant) := by
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace (ZMod 2) (Pi.basisFun (ZMod 2) (Fin 320))]
  change Matrix.trace (LinearMap.toMatrixAlgEquiv' (ρ _)) = _
  simp only [map_mul, map_pow]
  change Matrix.trace ((LinearMap.toMatrix' (ρ actorA) *
    LinearMap.toMatrix' (ρ actorB)) ^ 5 * LinearMap.toMatrix' (ρ actorB)) = _
  rw [hρ.1, hρ.2]

/-- A trace certificate distinguishes the actual native representations, with
the literal quotient-free action and word conventions retained. -/
theorem inequivalent_of_realizes (ht : TraceSeparation)
    (ρ σ : Representation (ZMod 2) M24 Space)
    (hρ : Realizes false ρ) (hσ : Realizes true σ) : IsEmpty (ρ.Equiv σ) := by
  constructor
  intro e
  apply ht
  have h := congrFun (Representation.char_iso e) ((actorA * actorB) ^ 5 * actorB)
  simpa only [character_word_of_realizes false ρ hρ,
    character_word_of_realizes true σ hσ] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair
