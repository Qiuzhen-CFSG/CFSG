module

public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts.LocalCalculations.ComponentBorels.Defs
public import Theory.SpecificGroups.PSL3.CartanActions.RootTorusControl

/-!
# The compatible matrix placement for the ordinary PSL₃ branch

The placement records an actual model isomorphism: the Borel maps to L ∩ M,
the highest-root group lies in V, and the chosen cyclic group is the image
of `diag(a,1,a⁻¹)`. It includes no commutator or action-kernel conclusion.
The construction and the ambient commutator argument use this common marking.
Source: Aschbacher–Smith, E.6.11(3b) and E.6.25, printed pp.249–250,255.
-/

@[expose] public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
variable {G : Type*} [Group G]

/-- The source Borel, root group and chosen torus in one actual PSL₃ model. -/
def LinearThreeTorusPlacement (M V L Y : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 2 ^ n ∧ ∃ e : L ≃* PSL(3,F),
      (Matrix.PSL3.LinearThree.borel F).map (L.subtype.comp e.symm.toMonoidHom) = L ⊓ M ∧
      (Matrix.PSL3Even.UnipotentGeometry.projectiveCenter F).map
        (L.subtype.comp e.symm.toMonoidHom) ≤ V ∧
      Y = (Matrix.PSL3.CartanActions.RootTorusControl.rootTorus F).range.map
        (L.subtype.comp e.symm.toMonoidHom)

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.CommutingLifts
