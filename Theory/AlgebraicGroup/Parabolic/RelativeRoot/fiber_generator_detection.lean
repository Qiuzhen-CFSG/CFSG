module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_torus_weight_generator_detection

/-!
Generator detection for a nonsingular relative-root fiber.  A nonzero invariant
submodule contains a nonzero coordinate vector by the torus-weight extraction
theorem: distinct relative roots are separated by coroot pairings, so successive
Chevalley torus operators eliminate all but one coordinate.  Packaging the
remaining root and scalar gives exactly the generator-detection predicate used
by the abstract orbit-span irreducibility criterion.  The extraction is in fact
characteristic-free; nonsingularity is retained here because it is the hypothesis
needed by the subsequent Chevalley root-string orbit argument.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

public theorem RelativeRootFiberModule.generator_detection
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (_hNonsingular : ¬ IsUSingular S.classification (ringChar k))
    (W : Submodule k M.V)
    (hW : IsInvariantSubmodule M.representation W)
    (hW0 : W ≠ ⊥) :
    ∃ z : FiberIndex S × k, z.2 ≠ 0 ∧ M.rootVector z ∈ W := by
  obtain ⟨γ, t, ht, htW⟩ :=
    M.exists_rootVector_mem_of_invariant_submodule S W hW hW0
  exact ⟨(γ, t), ht, htW⟩

end Theory.AlgebraicGroup
