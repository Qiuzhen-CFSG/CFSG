module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Setup
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import Theory.SpecificGroups.OrthogonalFourBinary.SingularOrbit

/-!
# Comparing the quadratic and wreath-coordinate natural actions

The source's four-space is the orthogonal sum of its two definite planes.
`orthogonalCoordinateValue` evaluates the sum of their anisotropic forms in
the existing matrix-and-coordinate-permutation model. A comparison witness
identifies this value with the actual quadratic form, retains the compatible
surjective conjugation action, and marks the chosen definite plane.

This is the shared intermediate contract for the orbit construction and the
two-case centralization argument. Its existence is a proof obligation, not
an earlier-source hypothesis or an abstract group-family identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1121–1122 and 1141.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

open Subgroup
open scoped IsMulCommutative

/-- The sum of the two definite binary plane forms in the existing coordinates. -/
def orthogonalCoordinateValue (v : OrthogonalVector) : ZMod 2 :=
  OrthogonalFourBinary.form
    (((v 1).toAdd 0, (v 1).toAdd 1),
      ((v (Multiplicative.ofAdd 1)).toAdd 0, (v (Multiplicative.ofAdd 1)).toAdd 1))

variable {G : Type*} [Group G] {M V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Actual coordinates, equivariant for the full action and compatible with
both the quadratic form and the definite plane used to define `S`. -/
structure OrthogonalCoordinateModel (d : NaturalOrthogonalAction M V) (P : Subgroup G) where
  action : CFSG.Quasithin.Chapter15.Section03.NaturalOrthogonalAction M V
  form_eq : ∀ v : V, d.form (Additive.ofMul v) =
    orthogonalCoordinateValue (action.coordinates v)
  plane_eq : ∃ i : OrthogonalPlaneIndex, P = action.plane i

end CFSG.Quasithin.Chapter15.Section03.FusionCore
