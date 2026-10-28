module

public import CFSG.Quasithin.ClassificationModels

/-!
# The exact model conclusion of Theorem 2.4.1

Aschbacher–Smith, printed p.527, with proof ending on p.550, gives PSL₂(p)
for p > 7 a Fermat or Mersenne prime, PSL₃(3), or M₁₁. These alternatives
retain actual group isomorphisms and the strict prime bound. Their inclusion
in the output of Theorem 2.1.1 is independent of the missing §2.4 recognition
proof; this file does not assert that recognition theorem.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2

/-- All and only the model alternatives stated in source Theorem 2.4.1. -/
def IsTheorem241Model (G : Type*) [Group G] : Prop :=
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧ 7 < p ∧ ClassicalGroup.IsPSL G 2 p) ∨
    ClassicalGroup.IsPSL G 3 3 ∨ Nonempty (G ≃* Sporadic.Mathieu.M11)

/-- The nonempty Γₑ₀ conclusion feeds the exact chapter classification. -/
theorem IsTheorem241Model.toTheorem211Model {G : Type*} [Group G]
    (h : IsTheorem241Model G) : ClassificationModels.IsTheorem211Model G := by
  rcases h with ⟨p, hp, hlarge, he⟩ | he | he
  · exact .linear_prime p hp hlarge he
  · exact .linear_three he
  · exact .mathieu_eleven he

end CFSG.Quasithin.Chapter2
