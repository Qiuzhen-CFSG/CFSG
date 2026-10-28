module

public import Theory.Mathieu.M12.SmallParabolicPair.FirstCore
public import Theory.LinearAlgebra.QuadraticForm.BinaryCubicOrbits

/-!
# Marked quotient geometry required by the M₁₂ cover argument

This contract retains the actual quaternion factors, the conjugation action
of the checked cubic element, and the two-residual of the marked involution
centralizer in the Witt-design M₁₂. The first three cubic orbits are marked
by their actual ambient conjugacy classes; the last two are the quaternion
axes. The extra centralizer involution must belong to the central class.

The record only specifies the model calculation still to be constructed.
It is not an assertion of existence, an involution table, or a covering
result. The core and cubic action themselves are already proved in the
imported `FirstCore` development.

Source: Aschbacher–Smith, I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair
open Subgroup Theory.LinearAlgebra.BinaryCubicOrbits

/-- The actual embedded O²(C_M₁₂(z)). -/
noncomputable def coverResidual : Subgroup M12 :=
  (pResidual 2 firstParabolic).map firstParabolic.subtype

/-- Geometric model input for the central-cover calculation, with actual maps. -/
structure CoverOrbitData where
  coordinates : core →* Multiplicative Space
  coordinates_surjective : Function.Surjective coordinates
  coordinates_ker : coordinates.ker = center core
  left_axis : ∀ r : core, r ∈ coreQuaternionData.left ↔ (coordinates r).toAdd.2 = 0
  right_axis : ∀ r : core, r ∈ coreQuaternionData.right ↔ (coordinates r).toAdd.1 = 0
  cubic_equivariance : ∀ r : core,
    (coordinates (residualCoreAction residualCubic r)).toAdd = cubic (coordinates r).toAdd
  square_mark : ∀ r : core,
    (r : M12) ^ 2 = z ↔ quaternionSquare (coordinates r).toAdd = 1
  orbit_order : ∀ (j : Fin 5) (k : Fin 3) (r : core),
    (coordinates r).toAdd = orbit j k →
      orderOf (r : M12) = if j = 3 ∨ j = 4 then 4 else 2
  central_fusion : ∀ (k : Fin 3) (r : core),
    (coordinates r).toAdd = orbit 2 k → IsConj z (r : M12)
  noncentral_fusion : ∀ (j : Fin 5) (k : Fin 3) (r : core),
    j = 0 ∨ j = 1 → (coordinates r).toAdd = orbit j k → IsConj third (r : M12)
  residual_core : (pCore 2 coverResidual).map coverResidual.subtype = core
  residual_card : Nat.card coverResidual = 96
  extra : M12
  extra_order : orderOf extra = 2
  extra_mem : extra ∈ firstParabolic
  extra_not_mem : extra ∉ coverResidual
  extra_fusion : IsConj z extra
  centralizer_generated : coverResidual ⊔ zpowers extra = firstParabolic

end Sporadic.Mathieu.M12SmallPair
