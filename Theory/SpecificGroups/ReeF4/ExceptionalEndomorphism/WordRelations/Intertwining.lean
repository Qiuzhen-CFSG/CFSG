module

public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Coordinates
public import Theory.SpecificGroups.ReeF4.Field
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4IntegralChevalleyRepresentation
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Simple
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport

/-!
# The exceptional F4 quotient-to-ideal intertwiner

In characteristic two, the concrete quotient-to-ideal matrix intertwines every
canonical integral F4 root curve with its exceptional image. The root duality
exchanges the geometric root lengths; the parameter is squared precisely on
the short roots.

The proof combines the positive and negative simple-root coefficient identities
from `Simple` with `Transport`'s comparison of canonical root routes. Integral
Tits words transport the simple identities, and the signs between different
routes disappear in characteristic two. All simple-root premises of that
transport theorem are discharged here for the existing `F4Chevalley.rootCurve`.

The final specialization applies to every Ree coefficient field, including
`m = 0`. This is the matrix comparison for the exceptional isogeny underlying
the Ree family in Aschbacher–Smith, Remark A.2.4 (`refs/quasithin.pdf`), using
the integral Chevalley construction of Steinberg, *Lectures on Chevalley Groups*.
-/

public section

open Theory.AlgebraicGroup
open scoped Classical Matrix

namespace ReeF4.WordRelations

/-- The concrete exceptional intertwining identity for every F4 root over any
commutative ring of characteristic two. -/
theorem quotientToIdeal_intertwines_rootCurve {K : Type*} [CommRing K] [CharP K 2]
    (r : F4Chevalley.Root) (t : K) :
    quotientToIdeal * (F4Chevalley.rootCurve r t : Matrix Coordinate Coordinate K) =
      (F4Chevalley.rootCurve (exceptionalRootPermutation r) (exceptionalParameter r t) :
        Matrix Coordinate Coordinate K) * quotientToIdeal :=
  quotientToIdeal_intertwines_all_roots_of_simple intertwines_simple intertwines_neg_simple r t

/-- The all-root quotient-to-ideal identity over every Ree coefficient field. -/
theorem intertwines_rootCurve (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    quotientToIdeal * (F4Chevalley.rootCurve r t :
        Matrix Coordinate Coordinate (CoefficientField m)) =
      (F4Chevalley.rootCurve (exceptionalRootPermutation r) (exceptionalParameter r t) :
        Matrix Coordinate Coordinate (CoefficientField m)) * quotientToIdeal :=
  quotientToIdeal_intertwines_rootCurve r t

end ReeF4.WordRelations
