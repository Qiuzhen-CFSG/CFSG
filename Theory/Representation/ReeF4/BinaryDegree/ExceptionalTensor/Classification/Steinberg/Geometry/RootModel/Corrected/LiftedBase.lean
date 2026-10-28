module
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.CorootConvention
import all Theory.AlgebraicGroup.RootSystems.F4RootPairingULift

/-!
# Public equations for the transported standard F4 base

This is an intentional internal proof extension of `F4RootPairingULift`:
`import all` accesses its chosen lift and base only to prove the following
public equations. No existing definition is exposed or modified. Consumers
use these equations to compare their literal labels to the transported base.
Source: the standard coordinate root pairing in GLS3 Section 1.8.
-/

public noncomputable section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
universe u

theorem lifted_pairing (r s : TypeF4RootIndexULift.{u}) :
    (typeF4RootPairing.pairingIn ℤ r.down s.down : ℝ) =
      typeF4RootPairingULift.pairing r s :=
  typeF4RootPairing.algebraMap_pairingIn ℤ r.down s.down

theorem lifted_reflect (r s : TypeF4RootIndexULift.{u}) :
    (⟨typeF4RootPairing.reflectionPerm r.down s.down⟩ : TypeF4RootIndexULift.{u}) =
      typeF4RootPairingULift.reflectionPerm r s := by rfl

theorem lifted_mem_base (r : TypeF4RootIndexULift.{u}) :
    r.down ∈ typeF4RootPairing_base.support ↔ r ∈ typeF4RootPairingULift_base.support := by
  rw [typeF4RootPairingULift_base, RootPairing.Base.mem_mapEquiv_support]
  rfl

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
