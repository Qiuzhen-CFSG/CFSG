module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiberModule_rational
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_generator_detection
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_full_levi_orbit_span
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible

/-!
# Irreducibility of relative-root fiber modules

For a nonsingular relative-root fiber, a nonzero invariant submodule contains
a nonzero root-vector generator by torus-weight detection.  The full-Levi
orbit-span theorem then says that this generator spans the whole fiber.  The
abstract orbit-span criterion combines these two source-specific inputs, and
the regular-conjugation construction supplies rationality.  This is the
source-level irreducibility result used by the relative-root representation
construction; it does not depend on the numbered Theorem 1.14.7.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- Every relative-root fiber module is rationally irreducible in
nonsingular characteristic. -/
public theorem RelativeRootFiberModule.isIrreducibleRepresentation
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (hNonsingular : ¬ IsUSingular S.classification (ringChar k)) :
    IsIrreducibleRepresentation M.representation := by
  refine ⟨M.isRationalRepresentation, ?_⟩
  apply isAlgebraicallyIrreducibleRepresentation_of_generator_detection_of_orbit_span
    M.representation M.rootVector (fun z => z.2 ≠ 0)
  · exact M.generator_detection S hNonsingular
  · intro z hz
    exact M.full_levi_orbit_span S hNonsingular z hz

end Theory.AlgebraicGroup
