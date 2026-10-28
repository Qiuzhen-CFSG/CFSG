module

public import Theory.Representation.SL2FourNaturalOrbits.BorelDualCore

/-!
# Conjugation coordinates on the intrinsic Borel two-core

The established equality of the embedded two-core with the upper root group
identifies the intrinsic pCore subtype with that root. Its existing field
coordinates intertwine literal Borel conjugation and the checked core action.
This is subtype transport, using the model certification in BorelDualCore.

Source application: Aschbacher--Smith 13.5.22(2), p.924/PDF p.941.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Representation.SL2FourNatural.BorelDualCore
open BorelFactors
def borelCoreEquiv : pCore 2 B0 ≃* U0 :=
  ((pCore 2 B0).equivMapOfInjective B0.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr twoCoreIn_B0)

def borelCoreCoordinates : pCore 2 B0 ≃* Multiplicative F :=
  borelCoreEquiv.trans Representation.SL2FourNatural.BorelDualCore.upperCoordinates

theorem borelCoreCoordinates_equivariant (b : B0) (x : pCore 2 B0) :
    (borelCoreCoordinates (MulAut.conjNormal b x)).toAdd =
      coreAction b (borelCoreCoordinates x).toAdd := by
  exact coordinateAction_equivariant U0 Representation.SL2FourNatural.BorelDualCore.upperCoordinates b (borelCoreEquiv x)

end Representation.SL2FourNatural.BorelDualCore
