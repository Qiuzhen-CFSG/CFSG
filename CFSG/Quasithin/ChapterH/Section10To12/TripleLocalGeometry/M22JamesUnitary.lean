module

public import CFSG.Quasithin.ChapterH.Section10To12.TripleLocalGeometry
public import Theory.Representation.Mathieu.M22James.Unitary

/-!
# The concrete Hermitian input for H.12 local geometry

The genuine native triple cover now supplies the faithful special-unitary
action required by `HermitianRestrictionInput`. Its compatibility proposition
is the literal column-action equation on the original binary module, and the
following theorem proves it using the constructed coordinate equivalence.
The imported realization also retains scalar compatibility and the invariant
binary quadratic form with its Hermitian diagonal identity.

This discharges the concrete unitary-model input in Aschbacher–Smith H.12.1(2),
printed pp.393–394. Transport to an arbitrary `IsTripleM22` component and the
remaining local-geometry clauses belong to their existing assembly owners.
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.ChapterH.Section10To12

open Sporadic.Mathieu
open M22TripleCover
open M22TripleCover.Unitary
open scoped Matrix

/-- The geometry input uses the genuine cover and its original binary representation. -/
def nativeHermitianRestrictionInput : HermitianRestrictionInput M22TripleCover where
  action := unitaryAction
  faithful := unitaryAction_faithful
  compatible := ∀ (g : M22TripleCover) (v : BinarySpace),
    ((unitaryAction g).val : Matrix (Fin 6) (Fin 6) Theory.SpecificGroups.U6Two.Field) *ᵥ
      standardCoordinates v = standardCoordinates (binaryRepresentation g v)

/-- The compatibility field is proved for the actual matrix action, not a family label. -/
theorem nativeHermitianRestrictionInput_compatible : nativeHermitianRestrictionInput.compatible :=
  unitaryAction_intertwines

end CFSG.Quasithin.ChapterH.Section10To12
