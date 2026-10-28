module

public import Theory.SpecificGroups.Janko3.Model.Order.TerminalSteps

/-!
# The order-sixteen terminal subgroup in the J₃ chain

Six signed generators permute sixteen word representatives. Their images of
point 2 are distinct. The complete permutation identities are checked by the
kernel; the word-subgroup cardinality theorem then gives order sixteen.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3.OrderCertificate
open Theory.GroupTheory
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option Elab.async false

private def L3Gen : Fin 0 → Equiv.Perm (Fin 6156) := Fin.elim0
private def L3Inv : Fin 0 → Fin 0 := Fin.elim0
private theorem L3Inv_spec (i : Fin 0) : L3Gen (L3Inv i) = (L3Gen i)⁻¹ := Fin.elim0 i

public theorem H2_card : Nat.card H2 = 16 := by
  have h := wordSubgroup_card_eq_mul_next
    L2Gen L2Inv L2Inv_spec L3Gen L3Inv L3Inv_spec
    L2Rep L2Act (fun _ _ => []) (2 : Fin 6156) L2Point (0 : Fin 16)
    L2Rep_mem
    (wordSubgroup_le_of_gen_mem (fun i => Fin.elim0 i))
    L2Rep_base L2Rep_point L2Point_injective
    (wordSubgroup_fix_of_gen_fix L3Gen L3Inv L3Inv_spec (fun i => Fin.elim0 i))
    (fun i r => by simpa only [evalWord, mul_one] using L2Step i r)
  simpa only [H2, wordSubgroup_fin_zero_card, Nat.mul_one] using h

/-- Every element of the terminal subgroup has a certified word representative. -/
public theorem H2_rep (g : H2) : ∃ r, (g : Equiv.Perm (Fin 6156)) = L2Rep r := by
  obtain ⟨w, hw⟩ := g.property
  suffices ∃ r, evalWord L2Gen w = L2Rep r by simpa only [hw] using this
  clear hw
  induction w with
  | nil => exact ⟨0, L2Rep_base.symm⟩
  | cons i w ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨L2Act i r, by rw [evalWord, hr, L2Step]⟩

/-- Fixing the third base point forces an element of the terminal subgroup to be one. -/
public theorem H2_base_trivial (g : H2) (h : (g : Equiv.Perm (Fin 6156)) 2 = 2) : g = 1 := by
  obtain ⟨r, hr⟩ := H2_rep g
  have hp : L2Point r = L2Point 0 := by
    rw [← L2Rep_point, ← hr, h]
    rfl
  have hidx := L2Point_injective hp
  rw [hidx, L2Rep_base] at hr
  exact Subtype.ext hr

end Sporadic.Janko3.OrderCertificate
