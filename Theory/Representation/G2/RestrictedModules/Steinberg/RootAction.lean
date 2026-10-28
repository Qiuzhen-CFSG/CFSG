module

public import Theory.Representation.G2.RestrictedModules.Steinberg.Construction

/-!
# Root formulas on the level-two G₂ Steinberg carrier

The six natural root matrices, in Wilson's order A through F, have explicit
polynomial coefficients. Taking their tensor cube gives a single coordinate
formula for every root parameter on the actual highest-weight orbit carrier.
The inclusion into the ambient tensor cube is injective, so these coordinates
specify the restricted action completely. The sparse root formulas re-exported
by `Steinberg.OrbitClosure` give its action on a 64-element spanning family.

Source: GLS3, 2.8.7 and Example 2.8.10(g), using the attributed ATLAS natural
root formulas. These are the level-two factor's root actions for subsequent
Frobenius tensor products.
-/

@[expose] public noncomputable section
open scoped BigOperators
namespace Atlas.G2.Restricted.Steinberg
variable (F : Type*) [Field F] [CharP F 2]

/-- The explicit coefficients of the six natural root matrices, ordered A through F.
The Steinberg root matrices are their tensor cubes restricted to the orbit carrier. -/
def rootCoefficient (r : Fin 6) (a : F) (i j : Fin 6) : F :=
  let v := e F j
  ![![v 0 + a * v 4, v 1 + a * v 5, v 2, v 3, v 4, v 5],
    ![v 0 + a * v 3, v 1, v 2 + a * v 5, v 3, v 4, v 5],
    ![v 0 + a^2 * v 5, v 1 + a * v 3, v 2 + a * v 4, v 3, v 4, v 5],
    ![v 0 + a * v 2, v 1 + a^2 * v 4, v 2, v 3 + a * v 5, v 4, v 5],
    ![v 0, v 1 + a * v 2, v 2, v 3 + a * v 4, v 4, v 5],
    ![v 0 + a * v 1, v 1, v 2 + a^2 * v 3, v 3, v 4 + a * v 5, v 5]] r i

private theorem rootCoefficient_eq (r : Fin 6) (a : F) (i j : Fin 6) :
    rootCoefficient F r a i j =
      NaturalCoordinates.action F
        (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) (e F j) i := by
  fin_cases r <;> simp [rootCoefficient]

/-- Explicit root-action formulas in the faithful ambient tensor coordinates,
valid for every parameter and every vector in the 64-dimensional carrier. -/
theorem coordinates_action_root (r : Fin 6) (a : F) (v : Space F) (i j k : Fin 6) :
    coordinates F (action F (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) v).val
        (i, j, k) =
      ∑ p : Fin 6 × Fin 6 × Fin 6,
        coordinates F v.val p * rootCoefficient F r a i p.1 *
          rootCoefficient F r a j p.2.1 * rootCoefficient F r a k p.2.2 := by
  simpa only [action_val, rootCoefficient_eq] using
    coordinates_ambientAction F
      (![rootA a, rootB a, rootC a, rootD a, rootE a, rootF a] r) v.val i j k

end Atlas.G2.Restricted.Steinberg
