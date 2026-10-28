module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Basic
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Faithfulness

/-!
# The finite four-dimensional Hermitian model

This interface exports the explicit quadratic finite field, its Frobenius
fixed subfield, the Hermitian matrix coordinates, the determinant quadratic
form and its faithful SL₂ action, for every positive extension parameter `n`.
The determinant has nonsingular polar form and Witt index one:
`form_nonsingular`, `singular_finrank_le_one` and `exists_singular_line`
give the explicit geometric characterization of minus type. The equivalences
`sl2EquivActionImage` and `psl2EquivActionImage` identify these groups with
the actual matrix-action image, with their action formulas proved in
`FiniteModel.Faithfulness`.

The final lemma specializes Hermitian descent to the constructed fields and
action. It leaves the ambient tensor cohomology hypotheses explicit for the
cohomology consumer to discharge; the field, form, geometry and group
identifications above are unconditional.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419).
See the three imported modules for the construction and proof details.
-/

public section

namespace Representation.OrthogonalFourMinus.FiniteModel

/-- Descent from the ambient twisted tensor action to the actual finite
four-dimensional minus-type Hermitian action. -/
lemma action_principal_surjective_of_tensor (n : ℕ) [NeZero n]
    (hfixed : OneCohomology.fixed (tensorAction (conjugation n)) = ⊥)
    (hprincipal : Function.Surjective
      (OneCohomology.principal (tensorAction (conjugation n)))) :
    Function.Surjective (OneCohomology.principal (action n)) :=
  principal_surjective_of_tensor (conjugationAlg n) (conjugation_involutive n)
    hfixed hprincipal

end Representation.OrthogonalFourMinus.FiniteModel
