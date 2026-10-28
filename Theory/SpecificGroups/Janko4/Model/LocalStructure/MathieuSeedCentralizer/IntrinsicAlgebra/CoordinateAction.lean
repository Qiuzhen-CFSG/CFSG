module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Action

/-!
# Transport of the intrinsic form action to ten coordinates

A genuine basis of `radicalForms` gives a homomorphism to invertible ten by ten
matrices. The entry and column-action formulas fix its convention, and transport
does not change its kernel. The basis is an explicit input here; its construction
from the literal ten forms is a separate finite certificate.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

abbrev TenMatrix := Matrix (Fin 10) (Fin 10) (ZMod 2)

/-- Coordinates of the actual full-centralizer action in a certified basis. -/
noncomputable def radicalMatrixAction (b : Module.Basis (Fin 10) (ZMod 2) radicalForms) :
    centralizer →* TenMatrixˣ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp radicalAction

theorem radicalMatrixAction_entry (b : Module.Basis (Fin 10) (ZMod 2) radicalForms)
    (c : centralizer) (i j : Fin 10) :
    (radicalMatrixAction b c : TenMatrix) i j =
      b.repr ((radicalAction c : Module.End (ZMod 2) radicalForms) (b j)) i :=
  LinearMap.toMatrixAlgEquiv_apply b _ i j

theorem radicalMatrixAction_mulVec (b : Module.Basis (Fin 10) (ZMod 2) radicalForms)
    (c : centralizer) (R : radicalForms) :
    (radicalMatrixAction b c : TenMatrix) *ᵥ b.repr R =
      b.repr ((radicalAction c : Module.End (ZMod 2) radicalForms) R) :=
  LinearMap.toMatrix_mulVec_repr b b _ R

theorem radicalMatrixAction_ker (b : Module.Basis (Fin 10) (ZMod 2) radicalForms) :
    (radicalMatrixAction b).ker = radicalAction.ker :=
  MonoidHom.ker_comp_of_injective radicalAction
    (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom)
    (Units.map_injective (LinearMap.toMatrixAlgEquiv b).injective)

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
