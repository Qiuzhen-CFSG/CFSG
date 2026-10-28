module

public import Theory.SpecificGroups.Janko3.Model.Order.Level1.Checks
public import Theory.SpecificGroups.Janko3.Model.Order.Level1.Assembly

/-!
# The certified 510-point step in the concrete J3 stabilizer chain

The published Schreier transitions decompose every level-1 word as a
transversal representative times a terminal element. Their distinct images of
point 1 identify the second point stabilizer and give index 510. The certified
terminal order sixteen therefore gives order 8160 for the level-1 subgroup.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory

public theorem L1Step (i : Fin 4) (r : Fin 510) :
    L1Gen i * L1Rep r = L1Rep (L1Act i r) * evalWord L2Gen (L1Factor i r) :=
  Level1.step_of_forward Level1.forwardSteps i r

public theorem H1_card_step : Nat.card H1 = 510 * Nat.card H2 :=
  Level1.card_step_of_step L1Step

public theorem H2_eq_stabilizer :
    H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156) :=
  Level1.stabilizer_of_step L1Step

public theorem H1_card : Nat.card H1 = 8160 := by
  rw [H1_card_step, H2_card]

end Sporadic.Janko3.OrderCertificate
