module
public import Theory.SpecificGroups.ReeF4.DerivedTits.Realization.SimpleData
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Intertwining.Transport.Curves

/-!
# Explicit positive-root routes for the Parrott words

Each row of the existing positive F₄ table is reached from a specified simple
root by a word in simple reflections. Endpoints are proved in Euclidean
coordinates, so the characteristic-two transport theorem applies to the actual
canonical root curves without evaluating their classically chosen routes.

Source: GLS3 §§2.3–2.4 and Parrott (1972), p.683; the candidate routes are
recorded in `Realization/source/README.md`. Words act rightmost first.
-/

@[expose] public section
noncomputable section
namespace ReeF4.DerivedTits.Realization.TransportComparison
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open Parabolics.RadicalCoordinates.FixedCoordinates

/-- The positive-root slots in the order of `RootPartition.table`. -/
def rootSlot : Fin 24 → Slot .positive :=
  show Fin 24 → (Fin 4 × Fin 2) ⊕ (Fin 4 × Fin 4) from
  ![.inl (0,0), .inl (0,1), .inl (1,0), .inl (1,1),
    .inl (2,0), .inl (2,1), .inl (3,0), .inl (3,1),
    .inr (0,0), .inr (0,1), .inr (0,2), .inr (0,3),
    .inr (1,0), .inr (1,1), .inr (1,2), .inr (1,3),
    .inr (2,0), .inr (2,1), .inr (2,2), .inr (2,3),
    .inr (3,0), .inr (3,1), .inr (3,2), .inr (3,3)]

def positiveRoot (i : Fin 24) : F4Chevalley.Root :=
  ((rootBlocks .positive).roots (rootSlot i)).val

theorem positiveRoot_val (i : Fin 24) : (positiveRoot i).val = RootPartition.table i := by
  have hi : ∀ i, RootPartition.index .positive (rootSlot i) = i := by decide
  exact (rootBlocks_roots_val .positive (rootSlot i)).trans (congrArg RootPartition.table (hi i))

theorem positiveRoot_pos (i : Fin 24) : typeF4RootPairing_base.IsPos (positiveRoot i) :=
  ((rootBlocks .positive).roots (rootSlot i)).property

def pairIndex (i : Fin 4) (j : Fin 2) : Fin 24 := ⟨2 * i.val + j.val, by omega⟩
def quartetIndex (i j : Fin 4) : Fin 24 := ⟨8 + 4 * i.val + j.val, by omega⟩

theorem pairRoots_eq (i : Fin 4) (j : Fin 2) :
    pairRoots i j = positiveRoot (pairIndex i j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem quartetRoots_eq (i j : Fin 4) :
    quartetRoots i j = positiveRoot (quartetIndex i j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The simple source and the route to each positive table row. -/
def routeSimple : Fin 24 → Fin 4 :=
  ![0,3,0,2,0,2,0,2,1,2,2,1,1,2,2,0,0,2,2,0,0,2,2,0]

def routeWord : Fin 24 → List (Fin 4) :=
  ![[], [], [1,2,1], [2,3,1], [3,1,2,1], [2,3,0,1],
    [2,3,1,2,1], [1,2,3,0,1], [], [], [1], [2], [3,2], [0,1],
    [3,2,1,2,3,0,1], [0,1,2,3,1,2,1], [1], [3], [3,0,1],
    [3,2,1], [2,1], [3,1], [2,1,2,3,0,1], [1,2,3,1,2,1]]

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

/-- The displayed routes reach the actual roots used by the fixed blocks. -/
theorem route_target (i : Fin 24) :
    reflectionWord (P := typeF4RootPairing)
      ((routeWord i).map typeF4RootPairing_baseEquiv)
      (typeF4SimpleRootIndex (routeSimple i)) = positiveRoot i := by
  apply Subtype.ext
  rw [positiveRoot_val]
  fin_cases i <;> funext k <;> fin_cases k <;>
    norm_num [routeWord, routeSimple, reflectionWord, reflection_val,
      typeF4RootPairing_baseEquiv_val, typeF4SimpleRootIndex_val,
      reflectedVector, typeF4SimpleRoot, RootPartition.table,
      Matrix.cons_val_two, Matrix.cons_val_three]

/-- Positive canonical curves transported along the certified finite routes. -/
theorem rootCurve_route (i : Fin 24) :
    F4Chevalley.rootCurve (positiveRoot i) (1 : CoefficientField 0) =
      WordRelations.titsUnit ((routeWord i).map typeF4RootPairing_baseEquiv) *
        F4Chevalley.rootCurve (typeF4SimpleRootIndex (routeSimple i)) 1 *
      (WordRelations.titsUnit ((routeWord i).map typeF4RootPairing_baseEquiv))⁻¹ :=
  WordRelations.rootCurve_of_pos_transport _ (positiveRoot_pos i) _
    (typeF4RootPairing_baseEquiv (routeSimple i)) (route_target i) 1

end ReeF4.DerivedTits.Realization.TransportComparison
