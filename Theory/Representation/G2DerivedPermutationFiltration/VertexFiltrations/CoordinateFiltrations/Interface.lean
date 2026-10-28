module

public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.Data
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.CoordinateFiltrations.FlagTools

/-!
# Coordinate obligations for the two vertex-module flags

`FlagCoordinates` contains invariant subspaces, the literal successive
quotients, and linear coordinate isomorphisms intertwining the two actual
free generators with the displayed diagonal matrices. It asserts neither
irreducibility nor a factor-degree filtration. The separate matrix-algebra
spanning certificate supplies simplicity; the proved finite flag assembly
then yields the required filtration.

This is an intermediate certificate interface for Aschbacher–Smith G.7.2(3),
printed p.348. Both the coordinate and spanning obligations must be proved
before asserting an unconditional coordinate filtration.
-/

@[expose] public section

namespace G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

open Representation

/-- Concrete invariant flags and equivariant coordinates on their literal
successive quotients. No simplicity assertion is a field of this structure. -/
structure FlagCoordinates (i : Fin 2) where
  stage : ℕ → Subrepresentation (representation i)
  zero : stage 0 = ⊥
  last : stage (length i) = ⊤
  mono : ∀ m, m < length i → stage m ≤ stage (m + 1)
  coordinates (t : Factor i) :
    ((stage (t.val + 1)).toSubmodule ⧸
      (within (stage t.val) (stage (t.val + 1))).toSubmodule) ≃ₗ[ZMod 2]
      (Fin (degree i t) → ZMod 2)
  generator_coordinates : ∀ (t : Factor i) (j : Fin 2) v,
    coordinates t
      ((within (stage t.val) (stage (t.val + 1))).quotientRepresentation (FreeGroup.of j) v) =
    (factorMatrix i t j).mulVec (coordinates t v)

/-- Matrix-span verification and actual quotient coordinates together give
an actual simple-factor filtration. Both premises require independent proofs. -/
theorem filtration_of_certificates (i : Fin 2) (C : FlagCoordinates i)
    (hspan : ∀ (t : Factor i)
      (Q : Subalgebra (ZMod 2) (Matrix (Fin (degree i t)) (Fin (degree i t)) (ZMod 2))),
      (∀ j, factorMatrix i t j ∈ Q) → Q = ⊤) :
    FactorDegreeFiltration allowedDegrees (representation i) := by
  apply filtration_of_flag allowedDegrees (length i) C.stage C.zero C.last C.mono
  · intro m hm
    let t : Factor i := ⟨m, hm⟩
    exact irreducible_of_coordinate_matrices (degree_pos i t) FreeGroup.of
      (factorMatrix i t) (C.coordinates t) (C.generator_coordinates t) (hspan t)
  · intro m hm
    let t : Factor i := ⟨m, hm⟩
    have he := (C.coordinates t).finrank_eq
    rw [Module.finrank_fin_fun] at he
    change Module.finrank (ZMod 2)
      ((C.stage (t.val + 1)).toSubmodule ⧸
        (within (C.stage t.val) (C.stage (t.val + 1))).toSubmodule) ∈ allowedDegrees
    rw [he]
    exact degree_allowed i t

end G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
