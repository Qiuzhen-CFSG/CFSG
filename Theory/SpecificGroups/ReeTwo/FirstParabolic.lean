module

public import Theory.SpecificGroups.ReeTwo.Characters
public import Mathlib.GroupTheory.Nilpotent

/-!
# The first parabolic core of the Ree two Sylow model

The subgroup `C_S(Z₂(S))` is characteristic in the concrete Sylow group.
Consequently conjugation by the Sylow group defines a homomorphism into its
automorphism group. This is the specified two-subgroup against which an
ambient normalizer action must be compared.

Source: van Beek, *Fusion Systems and Rank 2 Simple Groups of Lie Type*
(2024), Proposition 3.1, p. 10. No automorphism census is assumed here.
-/

namespace ReeTwo.SylowModel

/-- The first distinguished subgroup in the q = 2 fusion analysis. -/
@[expose] public def firstParabolicCore : Subgroup SylowModel :=
  Subgroup.centralizer (Subgroup.upperCentralSeries SylowModel 2 : Set SylowModel)

public instance firstParabolicCore_characteristic : firstParabolicCore.Characteristic := by
  unfold firstParabolicCore
  infer_instance

/-- Conjugation by the Sylow model on its characteristic first parabolic core. -/
@[expose] public def firstParabolicAction : SylowModel →* MulAut firstParabolicCore :=
  (MulAut.characteristic firstParabolicCore).comp MulAut.conj

@[simp] public theorem firstParabolicAction_apply (s : SylowModel)
    (x : firstParabolicCore) :
    (firstParabolicAction s x : SylowModel) = s * x * s⁻¹ := rfl

end ReeTwo.SylowModel
