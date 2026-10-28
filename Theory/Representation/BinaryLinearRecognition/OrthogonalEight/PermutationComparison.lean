module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Uses the ATLAS exceptional-isomorphism construction, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.Representation.BinaryLinearRecognition.OrthogonalEight
public import Theory.Representation.BinaryPermutationNaturalStructure

/-!
# Comparing the two concrete deleted eight-point modules

The projection from the even-weight code to the natural permutation module
has exactly the constant line as kernel. Its first-isomorphism equivalence
compares the two literal quotient constructions. Composing with the retained
ATLAS hyperbolic coordinates gives an S₈-equivariant identification with
split orthogonal six-space, and hence the actual A₈ action identification.
No dimension-only recognition or abstract choice of group isomorphism is used.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.3.1 and the paragraph following 13.6.23, printed pp.83 and 933.
-/

public section
open Atlas.Order20160A8
namespace Representation.BinaryLinearRecognition

private noncomputable def projection : DeletedEight.evenCode →ₗ[ZMod 2]
    BinaryPermutation.natural (Fin 8) := BinaryPermutation.coreToNatural (Fin 8)

private theorem projection_surjective : Function.Surjective projection :=
  BinaryPermutation.coreToNatural_surjective

private theorem projection_kernel : projection.ker = DeletedEight.constants := by
  ext w
  change projection w = 0 ↔ w ∈ DeletedEight.constants
  rw [Subtype.ext_iff]
  change (Submodule.Quotient.mk w.val : BinaryPermutation.Deleted (Fin 8)) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, BinaryPermutation.constants, DeletedEight.constants,
    Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, congrArg Subtype.val ha⟩

private noncomputable def quotientToNatural : DeletedEight.W ≃ₗ[ZMod 2]
    BinaryPermutation.natural (Fin 8) :=
  (Submodule.quotEquivOfEq _ _ projection_kernel.symm).trans
    (projection.quotKerEquivOfSurjective projection_surjective)

private theorem quotientToNatural_mk (w : DeletedEight.evenCode) :
    quotientToNatural (Submodule.Quotient.mk w) = projection w := rfl

private theorem quotientToNatural_equivariant (g : Equiv.Perm (Fin 8)) (v : DeletedEight.W) :
    quotientToNatural (DeletedEight.quotientPerm g v) =
      BinaryPermutation.naturalRepresentation (Fin 8) g (quotientToNatural v) := by
  induction v using Submodule.Quotient.induction_on with
  | H w =>
    exact BinaryPermutation.coreToNatural_equivariant g w

/-- The literal natural eight-point module, identified with the retained split
quadratic six-space via the same deleted quotient as the ATLAS model. -/
noncomputable def naturalEightOrthogonalEquiv : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
    ClassicalOrthogonal.VectorD 3 (ZMod 2) :=
  quotientToNatural.symm.trans DeletedEight.splitEquiv.symm

/-- Full S₈ equivariance, with no change of the permutation actor. -/
theorem naturalEightOrthogonalEquiv_permutation (g : Equiv.Perm (Fin 8))
    (v : BinaryPermutation.natural (Fin 8)) :
    naturalEightOrthogonalEquiv (BinaryPermutation.naturalRepresentation (Fin 8) g v) =
      (DeletedEight.orthogonalHom g).val (naturalEightOrthogonalEquiv v) := by
  apply DeletedEight.splitEquiv.injective
  change DeletedEight.splitEquiv (DeletedEight.splitEquiv.symm
    (quotientToNatural.symm (BinaryPermutation.naturalRepresentation (Fin 8) g v))) =
      DeletedEight.splitEquiv (DeletedEight.splitEquiv.symm (DeletedEight.quotientPerm g
        (DeletedEight.splitEquiv (DeletedEight.splitEquiv.symm (quotientToNatural.symm v)))))
  simp only [LinearEquiv.apply_symm_apply]
  apply quotientToNatural.injective
  rw [LinearEquiv.apply_symm_apply, quotientToNatural_equivariant, LinearEquiv.apply_symm_apply]

/-- The restriction identifies the actual A₈ representation used by recognition. -/
theorem naturalEightOrthogonalEquiv_alternating (g : alternatingGroup (Fin 8))
    (v : BinaryPermutation.natural (Fin 8)) :
    naturalEightOrthogonalEquiv (BinaryPermutation.alternatingNaturalRepresentation (Fin 8) g v) =
      orthogonalEightAction g (naturalEightOrthogonalEquiv v) :=
  naturalEightOrthogonalEquiv_permutation g.val v

end Representation.BinaryLinearRecognition
