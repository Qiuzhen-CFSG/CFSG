module
public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
/-!
# A small binary count for the source Sylow catalogue

After fixing an involution with nonzero (0,1) entry in UT₅(2), commutation
and squaring determine two of another involution's entries. Its remaining
six entries satisfy `squareFamily`; at most 28 choices survive. The final
free central entry doubles this bound to 56. This is the finite calculation
in the proof of Aschbacher, *Sporadic Groups* (1994), 39.1(3), p.213.
The certificate checks 32 parameter choices and 64 vectors, not subgroups.
-/

public section
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
abbrev B := ZMod 2
@[expose] def squareFamily (x : Fin 5 → B) (y : Fin 6 → B) : Prop :=
  let f := y 0 * (x 0 * x 2) + x 0 * y 3 + y 1 * x 2
  let g := y 0 * (x 0 * x 3 + x 1 * x 4) + x 0 * y 4 + y 1 * x 3 + x 1 * y 5 + y 2 * x 4
  y 3 * y 5 = 0 ∧ y 0 * f + y 1 * y 3 = 0 ∧ f * y 5 = 0 ∧
    y 0 * g + y 1 * y 4 + y 2 * y 5 = 0 ∧
    x 2 * y 5 + y 3 * x 4 = 0 ∧ (x 0 * x 2) * y 5 + f * x 4 = 0
instance (x : Fin 5 → B) : DecidablePred (squareFamily x) := by
  intro y
  unfold squareFamily
  infer_instance
set_option maxRecDepth 4096 in
/-- At most 28 six-entry vectors satisfy the square and commutation equations. -/
theorem squareFamily_card : ∀ x : Fin 5 → B, x 2 * x 4 = 0 →
    Fintype.card { y : Fin 6 → B // squareFamily x y } ≤ 28 := by
  intro x
  fin_cases x <;> decide +kernel
end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
