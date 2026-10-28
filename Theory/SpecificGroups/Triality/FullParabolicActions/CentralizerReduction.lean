module

public import Theory.SpecificGroups.Triality.FullParabolicActions.Definitions
public import Theory.GroupTheory.FaithfulSupplementCentralizer

/-!
# Reducing the full-parabolic centralizer to its full-Levi root action

The full Levi supplements the two-group radical and has trivial two-core.
If its actual action on the radical is faithful, the inverse image of the
radical's inner automorphisms is trivial. Thus a centralizing element of
the full parabolic has no full-Levi component and lies in the radical.

The faithfulness premise is explicitly retained. It must be discharged by
the root action for each node before obtaining the local characteristic-two
conclusion of GLS3 Theorem 2.6.5(e) (`refs/KGroup/GLS3/chapter2.tex`).
The argument makes no perfectness assumption and includes q = 2.
-/

public section
namespace Triality.Standard.Parabolics

/-- The remaining premise is faithfulness of the actual full-Levi action. -/
theorem parabolic_centralizer_radical_le_of_fullLevi_faithful
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    (hfaithful : Function.Injective (fullLeviRadicalAction P a)) :
    parabolic P a ⊓ Subgroup.centralizer (radical P a : Set (Carrier P)) ≤
      radical P a := by
  rw [parabolic_eq_radical_sup_fullLevi P hp a]
  exact Subgroup.sup_inf_centralizer_le_of_faithful_supplement
    (radical P a) (fullLevi P a) (fullLevi_le_normalizer_radical P a)
    (RadicalCoordinates.radical_isPGroup P hp a) (fullLevi_twoCore_eq_bot P hp a) hfaithful

end Triality.Standard.Parabolics
