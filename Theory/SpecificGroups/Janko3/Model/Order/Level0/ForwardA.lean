module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Selection
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Part0
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Part1
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Part2
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA.Part3
import Mathlib.Tactic.FinCases

/-!
# Assembling the first J3 Schreier row for A

The algebraic transitions and the involution pairing reduce this row to four
independent parts, each containing 140 exceptional transitions. The second
stabilizer equality supplies the two-point base used to cancel paired factors.
The four checked parts now give `forwardRow0`, with precisely that equality
as its remaining input from the second Schreier step.
Source: ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0

/-- Assemble the full row from the four numerical certificates. -/
public theorem forwardRow0_of_parts
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (h : ∀ p, exceptionalAPart p) : ForwardRow 0 :=
  forwardRow0_of_exceptional hstab (exceptionalA_of_parts h)

/-- Every published forward A transition, using the second stabilizer equality
to recover the paired exceptional transitions. -/
public theorem forwardRow0
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156)) :
    ForwardRow 0 := by
  apply forwardRow0_of_parts hstab
  intro p
  fin_cases p
  · exact exceptionalAPart0
  · exact exceptionalAPart1
  · exact exceptionalAPart2
  · exact exceptionalAPart3

end Sporadic.Janko3.OrderCertificate.Level0
