module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardA
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB
public import Theory.SpecificGroups.Janko3.Model.Order.Level1Certificate

/-!
# The certified 6156-point step in the concrete J3 stabilizer chain

The checked forward rows and the independently proved second stabilizer
equality certify all four published Schreier transition rows. Word decomposition
then expresses every element of H0 as a transversal representative times an
element of H1. The distinct images of point 0 give index 6156 and identify H1
as its full stabilizer in H0, with the generators already defined by `L1Gen`.

Source: ATLAS J3G1-p6156B0, retained under `Model/data/`, and the concrete
transversal and factor words in `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory

/-- Every transition for the published level-0 transversal and factor words. -/
public theorem L0Step (i : Fin 4) (r : Fin 6156) :
    L0Gen i * L0Rep r = L0Rep (L0Act i r) * evalWord L1Gen (L0Factor i r) :=
  Level0.steps_of_forward
    (Level0.forwardRow0 H2_eq_stabilizer)
    (Level0.forwardRow1 H2_eq_stabilizer)
    H2_eq_stabilizer i r

/-- The first transversal has 6156 cosets of H1 in H0. -/
public theorem H0_card_step : Nat.card H0 = 6156 * Nat.card H1 :=
  Level0.card_step L0Step

/-- The concrete level-1 generators generate the full stabilizer of point 0 in H0. -/
public theorem H1_eq_stabilizer :
    H1 = H0 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (0 : Fin 6156) :=
  Level0.stabilizer_eq L0Step

end Sporadic.Janko3.OrderCertificate
