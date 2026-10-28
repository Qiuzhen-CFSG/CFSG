module

public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.Triality.FullParabolicActions.CentralizerReduction
public import Theory.SpecificGroups.Triality.FullParabolicActions.ArmsFaithfulAction
public import Theory.SpecificGroups.Triality.FullParabolicActions.CentralFaithfulAction

/-!
# Full-parabolic quotients and radical centralizers in binary triality

For either node, the full parabolic modulo its embedded prime-to-two
residual is cyclic. The proof uses the actual two torus coordinates and
the folded coroot words lying in the subsystem Levi, including q = 2.

The full Levi acts faithfully on the root radical for both nodes. The arms
calculation uses the highest-root character and the genuine PSL₂(q³) action;
the central calculation uses the root-string columns of SL₂(q) and torus
weights. Together with the trivial two-core of the full Levi, this gives
the centralizer bound inside the full parabolic. All results include q = 2
and retain the elementary restriction and its own central quotient.

Sources: GLS3 §2.4 and Theorem 2.6.5(e–g)
(`refs/KGroup/GLS3/chapter2.tex`); Aschbacher–Smith F.1.12(I)(4),
printed pp.263–264 (`refs/quasithin.pdf`).
-/

public section
namespace Triality.Standard.Parabolics

/-- Both genuine full Levi complements act faithfully on their root radicals. -/
theorem fullLeviRadicalAction_injective (P : Parameters) (hp : P.prime = 2) (a : Node) :
    Function.Injective (fullLeviRadicalAction P a) := by
  cases a with
  | arms => exact fullLeviRadicalAction_injective_arms P hp
  | central => exact fullLeviRadicalAction_injective_central P hp

/-- The centralizer of the radical inside either full parabolic lies in the radical. -/
theorem parabolic_centralizer_radical_le (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a ⊓ Subgroup.centralizer (radical P a : Set (Carrier P)) ≤
      radical P a :=
  parabolic_centralizer_radical_le_of_fullLevi_faithful P hp a
    (fullLeviRadicalAction_injective P hp a)

/-- The full-parabolic centralizer bound at every positive binary exponent,
including f = 1, without a perfectness assumption on the central Levi. -/
theorem parabolic_centralizer_radical_le_binary (f : ℕ) (hf : 0 < f) (a : Node) :
    parabolic (binaryParameters f hf) a ⊓
      Subgroup.centralizer
        (radical (binaryParameters f hf) a : Set (Carrier (binaryParameters f hf))) ≤
        radical (binaryParameters f hf) a :=
  parabolic_centralizer_radical_le _ rfl a

end Triality.Standard.Parabolics
