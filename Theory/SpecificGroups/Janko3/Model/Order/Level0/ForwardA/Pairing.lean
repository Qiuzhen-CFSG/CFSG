module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.Forward
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.Inverse

/-!
# Pairing the forward A transitions

The published A index table is an involution. Its paired factors cancel on
points 1 and 2, hence in H1 once the second stabilizer equality is available.
Consequently one transition in each two-cycle implies the other. This uses
only the second chain step, not the first stabilizer certificate being proved.
Source: ATLAS J3G1-p6156B0 and `Order/data/witnesses.json`.
-/

namespace Sporadic.Janko3.OrderCertificate.Level0
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option Elab.async false

/-- The transition at one representative in the A row. -/
public abbrev forwardAStep (r : Fin 6156) : Prop :=
  L0Gen 0 * L0Rep r = L0Rep (L0Act 0 r) * evalWord L1Gen (L0Factor 0 r)

public theorem act00 : ∀ r, L0Act 0 (L0Act 0 r) = r := by
  apply allFin
  decide +kernel

private theorem factor00_fix : ∀ r, ∀ j : Fin 2,
    (evalWord L1Gen (L0Factor 0 (L0Act 0 r)) * evalWord L1Gen (L0Factor 0 r))
      (if j = 0 then 1 else 2) = (if j = 0 then 1 else 2) := by
  apply allFin₂
  decide +kernel

public theorem factor00_cancel
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (r : Fin 6156) :
    evalWord L1Gen (L0Factor 0 (L0Act 0 r)) * evalWord L1Gen (L0Factor 0 r) = 1 := by
  let g : H1 := ⟨evalWord L1Gen (L0Factor 0 (L0Act 0 r)) * evalWord L1Gen (L0Factor 0 r), H1.mul_mem
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)
    (evalWord_mem_wordSubgroup L1Gen L1Inv L1Inv_spec _)⟩
  have h1 : (g : Equiv.Perm (Fin 6156)) 1 = 1 := factor00_fix r 0
  have h2 : (g : Equiv.Perm (Fin 6156)) 2 = 2 := factor00_fix r 1
  exact congrArg (fun k : H1 => (k : Equiv.Perm (Fin 6156)))
    (H1_base_trivial hstab g h1 h2)

/-- Recover the other half of an A two-cycle. -/
public theorem forwardAStep_of_partner
    (hstab : H2 = H1 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 6156)) (1 : Fin 6156))
    (r : Fin 6156) (h : forwardAStep (L0Act 0 r)) : forwardAStep r := by
  change L0Gen 0 * L0Rep r = L0Rep (L0Act 0 r) * evalWord L1Gen (L0Factor 0 r)
  apply mul_left_cancel (a := L0Gen 0)
  have ha : L0Gen 0 * L0Gen 0 = 1 := by
    change atlasA * atlasA = 1
    simpa only [pow_two] using atlasA_sq
  rw [← mul_assoc, ha, one_mul, ← mul_assoc, h, act00, mul_assoc,
    factor00_cancel hstab, mul_one]

end Sporadic.Janko3.OrderCertificate.Level0
