module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.AdjointRestriction.IntegralIntertwining.FirstOrder.StringLengths.RationalModel

/-!
# Checked rational E6–F4 string calculation

Two kernel-reduced finite certificates cover the pair and half-sign root
families. The input equations are precisely the E6 orthogonality conditions;
the half family also retains its even parity. The parent module proves that
these rational membership tests compute the actual bottom string lengths.

The certificates use ordinary kernel reduction, with no native evaluator or
coefficient table. The representative calculation was measured before checking
the complete families. Sources: GLS3 §§2.2–2.6; A.2.17, printed p.39.
-/

public section
namespace TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths
set_option maxRecDepth 4096 in
theorem pair_check (a b : Fin 8) (s t : Bool) (i : Fin 4) :
    a ≠ b → (pair a b s t) 0 + (pair a b s t) 1 = 0 →
      (pair a b s t) 1 - (pair a b s t) 2 = 0 → check (pair a b s t) i := by
  decide +kernel +revert

set_option maxRecDepth 4096 in
theorem half_check (ε : Fin 8 → Bool) (i : Fin 4) :
    (Finset.univ.filter (fun k => !(ε k))).card % 2 = 0 →
      (half ε) 0 + (half ε) 1 = 0 → (half ε) 1 - (half ε) 2 = 0 →
        check (half ε) i := by
  decide +kernel +revert

end TwistedE6.FoldedSubsystem.F4Identification.AdjointRestriction.StringLengths
