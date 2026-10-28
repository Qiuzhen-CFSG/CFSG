module
public import Theory.Representation.DegreeThreeFrattini

/-!
# The degree-three Frattini bound for the literal matrix action

The natural representation transports a faithful matrix embedding of an odd
characteristic two-group to the existing degree-three Frattini bound. The
odd ternary Hall-normalizer rows use precisely this matrix form.
Source: Aschbacher--Smith A.3.21(c) and 4.4.10, pp.55--56,621.
-/

public section
namespace Representation

/-- The bound on the literal natural matrix action. -/
theorem card_frattini_quotient_le_sixteen_of_injective_generalLinear_three
    {F P : Type*} [Field F] [Group P] [Finite P] {n : ℕ}
    (hP : IsPGroup 2 P) (f : P →* GL (Fin n) F)
    (hf : Function.Injective f) (h2 : (2 : F) ≠ 0) (hn : n ≤ 3) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  apply card_frattini_quotient_le_sixteen_of_faithful_degree_three hP
    ((generalLinearNatural n).comp f) ((generalLinearNatural_injective n).comp hf) h2
  simpa only [Module.finrank_pi, Fintype.card_fin] using hn


end Representation
