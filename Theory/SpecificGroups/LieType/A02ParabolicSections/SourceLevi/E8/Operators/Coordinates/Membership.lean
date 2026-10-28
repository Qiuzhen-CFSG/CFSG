module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E8.Operators.Coordinates.Data

/-!
# Explicit E8 membership witnesses

Finite integer certificates for the native E8 root catalogue (GLS3 §2.6).
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates.Certificates

def sign (a : Bool) : ℤ := if a then 1 else -1
def pair (i j : Fin 8) (a b : Bool) : Fin 8 → ℤ :=
  fun k => (if k = i then 2 * sign a else 0) + (if k = j then 2 * sign b else 0)
def half (ε : Fin 8 → Bool) : Fin 8 → ℤ := fun k => sign (ε k)
private instance (ε : Fin 8 → Bool) : Decidable (evenNegative ε) :=
  inferInstanceAs (Decidable (Even ((Finset.univ.filter fun i => !(ε i)).card)))
private def pairWitness (r : Fin 240) : Fin 8 × Fin 8 × Bool × Bool :=
  let p := (#[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7), (3, 4), (3, 5), (3, 6), (3, 7), (4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)] : Array (Fin 8 × Fin 8))[r.val / 4]!
  (p.1, p.2, decide (2 ≤ r.val % 4), decide (r.val % 2 = 1))
private def signs (r : Fin 240) (q : Fin 8) : Bool := decide (0 < coord r q)
theorem coord_pair_or_half : ∀ r : Fin 240,
    (∃ i j : Fin 8, ∃ a b : Bool, i ≠ j ∧ coord r = pair i j a b) ∨
      ∃ ε : Fin 8 → Bool, evenNegative ε ∧ coord r = half ε := by
  have hc : ∀ r : Fin 240,
      ((pairWitness r).1 ≠ (pairWitness r).2.1 ∧
        coord r = pair (pairWitness r).1 (pairWitness r).2.1 (pairWitness r).2.2.1 (pairWitness r).2.2.2) ∨
      (evenNegative (signs r) ∧ coord r = half (signs r)) := by decide +kernel
  intro r
  rcases hc r with hp | hh
  · exact Or.inl ⟨_, _, _, _, hp⟩
  · exact Or.inr ⟨_, hh⟩


end Theory.SpecificGroups.LieType.SourceLevi.E8.Operators.Coordinates.Certificates
