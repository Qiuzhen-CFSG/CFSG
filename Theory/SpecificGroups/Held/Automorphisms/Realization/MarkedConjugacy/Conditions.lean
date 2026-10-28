module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
import Mathlib.Tactic.FinCases

/-!
# Normalized pairs for the Held marked-subgroup calculation

After inner conjugation makes the image of `ab` a power `(ab)^k`, the image
`x` of the involution `a` determines the second generator as `x * (ab)^k`.
The remaining finite calculation asks whether each such pair satisfying the
seven actual ATLAS relators has a common fixed point for its three marked
words. It concerns elements of the exact permutation carrier, not an assumed
presentation isomorphism or automorphism classification.

This module specifies that calculation and proves how its point equations
imply containment of the automorphic marked subgroup in a point stabilizer.
It does not assert the finite calculation. The shared marked subgroup and
its three generators remain those of `MarkedSubgroup`.

Source: John Bray's `Model/Source/HeG1-P1.M`, its seven uncommented
relations and `M1 = <x, x^(y^2), x^(y^-2)>`; conjugation in that source
means `x^y = y^-1*x*y`.
-/

namespace Held.Realization.MarkedConjugacy

/-- Fixed-point equations for the three literal ATLAS marked words. -/
@[expose] public def PairFixes (x y : He) (p : Fin 2058) : Prop :=
  representation x p = p ∧
    representation ((y ^ 2)⁻¹ * x * y ^ 2) p = p ∧
    representation (y ^ 2 * x * (y ^ 2)⁻¹) p = p

/-- The finite calculation after normalizing the product of the generators. -/
@[expose] public def NormalizedPairFixedPoint : Prop :=
  ∀ (k : Fin 17) (x : He), orderOf x = 2 →
    (∀ i : Fin 7, relationWord x (x * (a * b) ^ k.val) i = 1) →
    ∃ p : Fin 2058, PairFixes x (x * (a * b) ^ k.val) p

/-- The three fixed-point equations imply fixation by the full image subgroup. -/
public theorem map_le_stabilizer_of_pairFixes (f : MulAut He) (p : Fin 2058)
    (hp : PairFixes (f a) (f b) p) :
    markedSubgroup.map f.toMonoidHom ≤ MulAction.stabilizer He p := by
  rw [Subgroup.map_le_iff_le_comap, markedSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  change representation (f (markedGenerator i)) p = p
  rcases hp with ⟨ha, hb, hc⟩
  fin_cases i
  · exact ha
  · simpa only [markedGenerator, map_mul, map_inv, map_pow] using hb
  · simpa only [markedGenerator, map_mul, map_inv, map_pow] using hc

end Held.Realization.MarkedConjugacy
