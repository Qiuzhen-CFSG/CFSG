module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives

/-!
# The rank-one models before the local Sylow restrictions

The rank-one paragraph in the proof of 15.3.37 first reduces 1.1.5(3) to
the models below. The local Sylow action then restricts the parameters and
the Borel action gives innerness. Separating these outputs allows those
two arguments to be proved independently. No classification is asserted here.

The quotient models in 15.3.43 follow from these actual component models
once triviality of the component two-core is established. Transport uses
the canonical quotient equivalence, not recognition by order.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1135 and 1139, using the six alternatives of 1.1.5(3), pp.501--502.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Candidates

/-- The models in the first rank-one case split on p.1135, before the
Sylow action forces even exponents or the exceptional small parameters.
The signed rank-three congruences are the opposite of the diagonal ones. -/
def RankOneInitialModel (L : Type*) [Group L] : Prop :=
  (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL L 2 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 2 ∧ ClassicalGroup.IsPSL L 3 (2 ^ n)) ∨
  (∃ n : ℕ, 0 < n ∧ 2 ^ n % 3 = 1 ∧ ClassicalGroup.IsPSU L 3 (2 ^ n)) ∨
  (∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL L 2 p)

/-- Transport to the precise quotient interface of 15.3.43. The source
model reduction must prove the two-core hypothesis as well as the model. -/
theorem RankOneInitialModel.toQuotient {L : Type*} [Group L]
    (h : RankOneInitialModel L) (hcore : pCore 2 L = ⊥) :
    RankOneQuotientModel L := by
  let e : (L ⧸ pCore 2 L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  rcases h with ⟨n, hn, hm⟩ | ⟨n, hn, hmod, hm⟩ | ⟨n, hn, hmod, hm⟩ | ⟨p, hp, hm⟩
  · exact Or.inl ⟨n, hn, hm.of_mulEquiv e⟩
  · exact Or.inr (Or.inl ⟨n, hn, hmod, hm.of_mulEquiv e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, hmod, hm.of_mulEquiv e⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hm.of_mulEquiv e⟩))

end CFSG.Quasithin.Chapter15.Section03.Candidates
