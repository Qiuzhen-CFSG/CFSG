module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-!
# Coordinates for the derived Witt design

This explicit embedding identifies eleven labels with the complement of zero
in twelve labels. `CompletionCertificate` checks its augmented concrete M11
blocks against the actual M12 block masks. Keeping these coordinates explicit
allows that certificate to compute without unfolding the hidden implementation
of the point-stabilizer isomorphism.

Source context: Aschbacher, *Sporadic Groups*, Exercise 6.6(6), the extension
from the eleven-point to the twelve-point Witt design.
-/

namespace Sporadic.Mathieu.M12WittUniqueness

/-- Coordinates used to compare the concrete eleven- and twelve-point designs. -/
@[expose]
public def pointEmbedding : Fin 11 ↪ Fin 12 where
  toFun := ![5, 1, 7, 8, 6, 4, 2, 3, 11, 9, 10]
  inj' := by decide +kernel

/-- The distinguished twelfth point is outside the embedded eleven points. -/
public theorem pointEmbedding_ne_zero : ∀ i, pointEmbedding i ≠ 0 := by decide +kernel

/-- Every point other than zero has an eleven-point coordinate. -/
public theorem pointEmbedding_surjective : ∀ x : Fin 12, x ≠ 0 →
    ∃ i, pointEmbedding i = x := by decide +kernel

end Sporadic.Mathieu.M12WittUniqueness
