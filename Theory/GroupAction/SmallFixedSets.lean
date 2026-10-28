module
public import Mathlib.GroupTheory.PGroup

/-!
# Fixed sets smaller than the acting prime

If a p-subgroup P is contained in another p-subgroup Q, the Q-fixed set
is contained in the P-fixed set. Their cardinalities are both congruent to
the cardinality of the finite ambient set modulo p. Hence they are equal
whenever P has fewer than p fixed points. No normality of P in Q is needed.

The source application is the odd-prime exact-two branch of GLS, Volume 4,
Chapter 2, Lemma 5.8: passing to a Sylow subgroup preserves its two fixed
points. See ZD SectionFive.TheoremTwo.ExactTwo.
-/

namespace IsPGroup

/-- Enlarging a p-subgroup preserves a fixed set of cardinality less than p. -/
public theorem fixedPoints_card_eq_of_le_of_card_lt
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hP : IsPGroup p P) (hQ : IsPGroup p Q) (hPQ : P ≤ Q)
    (hlt : Nat.card (MulAction.fixedPoints P X) < p) :
    Nat.card (MulAction.fixedPoints Q X) = Nat.card (MulAction.fixedPoints P X) := by
  let f : MulAction.fixedPoints Q X → MulAction.fixedPoints P X := fun x =>
    ⟨x.val, fun a => x.property (⟨a.val, hPQ a.property⟩ : Q)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : MulAction.fixedPoints P X => (z : X)) h
  have hle := Nat.card_le_card_of_injective f hf
  have hc := (hQ.card_modEq_card_fixedPoints X).symm.trans (hP.card_modEq_card_fixedPoints X)
  change Nat.card (MulAction.fixedPoints Q X) % p = Nat.card (MulAction.fixedPoints P X) % p at hc
  rwa [Nat.mod_eq_of_lt (lt_of_le_of_lt hle hlt), Nat.mod_eq_of_lt hlt] at hc

end IsPGroup
