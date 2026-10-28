module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Pairing

/-!
# Direct tree edges in the A row

When the published factor word is empty and one representative word is A
followed by the other, the transition follows immediately from A² = 1.
This handles 5110 transitions without recursively normalizing their words.
Source: the breadth-first transversal in `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory

@[expose] public def aTreeEdge (r : Fin 6156) : Prop :=
  L0Factor 0 r = [] ∧
    (L0RepWord (L0Act 0 r) = 0 :: L0RepWord r ∨
      L0RepWord r = 0 :: L0RepWord (L0Act 0 r))

public instance (r : Fin 6156) : Decidable (aTreeEdge r) :=
  inferInstanceAs (Decidable (_ ∧ _))

public theorem forwardAStep_of_tree (r : Fin 6156) (h : aTreeEdge r) : forwardAStep r := by
  have ha : L0Gen 0 * L0Gen 0 = 1 := by
    change atlasA * atlasA = 1
    simpa only [pow_two] using atlasA_sq
  change L0Gen 0 * evalWord L0Gen (L0RepWord r) =
    evalWord L0Gen (L0RepWord (L0Act 0 r)) * evalWord L1Gen (L0Factor 0 r)
  rcases h with ⟨hf, ht | ht⟩
  · rw [ht, hf]
    simp only [evalWord, mul_one]
  · rw [ht, hf]
    simp only [evalWord, ← mul_assoc, ha, one_mul, mul_one]

end Sporadic.Janko3.OrderCertificate.Level0
