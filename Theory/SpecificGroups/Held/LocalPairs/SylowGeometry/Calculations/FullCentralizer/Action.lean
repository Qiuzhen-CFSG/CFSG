module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative

/-!
# Commutation tests in the actual Held representative

A walk applies the listed generators successively. Commuting permutations
preserve endpoint equalities and inequalities. Four such tests at point zero
will restrict its image to two points. The words refer directly to the
representative, with no subgroup-recognition or center-order premise.

Source: ATLAS HeG1-p2058B0, HeG1-max3W1; GLS3 Table 5.3p.
-/

public section

namespace Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer

@[expose] def step (i : Fin 4) : Equiv.Perm (Fin 2058) := representation (generator i)
@[expose] def walk : List (Fin 4) → Fin 2058 → Fin 2058
  | [], x => x
  | i :: w, x => walk w (step i x)


@[expose] def CommutesGenerators (σ : Equiv.Perm (Fin 2058)) : Prop :=
  ∀ i x, σ (step i x) = step i (σ x)

lemma walk_commute (σ : Equiv.Perm (Fin 2058)) (hσ : CommutesGenerators σ)
    (w : List (Fin 4)) (x : Fin 2058) : σ (walk w x) = walk w (σ x) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [walk, ih, hσ i]

lemma eq_walk_iff (σ : Equiv.Perm (Fin 2058)) (hσ : CommutesGenerators σ)
    (w v : List (Fin 4)) (x : Fin 2058) :
    walk w (σ x) = walk v (σ x) ↔ walk w x = walk v x := by
  rw [← walk_commute σ hσ w, ← walk_commute σ hσ v]
  exact σ.injective.eq_iff

@[expose] def test0 (x : Fin 2058) : Prop :=
  walk [3] x = walk [] x ∧ walk [0] x = walk [] x ∧
  walk [1, 0] x ≠ walk [1] x ∧ walk [1, 2] x ≠ walk [1] x
instance (x : Fin 2058) : Decidable (test0 x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

end Held.LocalPairs.SylowGeometry.Calculations.FullCentralizer
