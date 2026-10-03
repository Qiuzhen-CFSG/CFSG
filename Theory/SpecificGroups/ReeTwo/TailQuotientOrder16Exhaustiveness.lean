module

public import Theory.SpecificGroups.ReeTwo.TailQuotientOrder16Certificate

/-!
# Exhaustiveness of the order-sixteen tail-quotient nodes

Every order-sixteen subgroup of the order-64 Ree two tail quotient equals
one of the 27 explicit nodes. Encode its elements as a finite set of coordinate
codes and apply the checked membership certificate. This supplies the
generators of a node inside the subgroup. The existing generation theorem
and equality of the two orders turn containment into equality.

Source: finite subgroup enumeration in the Shinoda coordinate model, as
specified in `SylowTailQuotient` and checked in
`TailQuotientOrder16Certificate`.
-/

namespace ReeTwo.TailQuotient.Order16Nodes
open Order16Certificate

/-- The 27 checked nodes exhaust the order-sixteen subgroups, with exact equality. -/
public theorem exhaustive (H : Subgroup Group) (hH : Nat.card H = 16) :
    ∃ i : Fin 27, H = node i := by
  classical
  let s : Finset (Fin 64) := Finset.univ.filter (fun n => coordinateElement n.val ∈ H)
  have mem_s (n : Fin 64) : n ∈ s ↔ coordinateElement n.val ∈ H := by simp [s]
  have hc (q : Group) : coordinateElement (code q).val = q := coordinateElement_code q
  let e : H ≃ ↥s :=
    { toFun := fun q => ⟨code q.val, (mem_s _).mpr (by rw [hc]; exact q.property)⟩
      invFun := fun n => ⟨coordinateElement n.val.val, (mem_s _).mp n.property⟩
      left_inv := fun q => Subtype.ext (hc q.val)
      right_inv := fun n => Subtype.ext (Fin.ext (coordinateCode_element n.val)) }
  have hs : s.card = 16 := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e, ← Nat.card_eq_fintype_card]
    exact hH
  have hzero : (0 : Fin 64) ∈ s := by
    apply (mem_s _).mpr
    have hz : coordinateElement 0 = 1 := coordinateCode_injective rfl
    change coordinateElement 0 ∈ H
    rw [hz]
    exact H.one_mem
  have hm (a b : Fin 64) (ha : a ∈ s) (hb : b ∈ s) : mulCode a b ∈ s := by
    apply (mem_s _).mpr
    change coordinateElement (coordinateCode _) ∈ H
    rw [coordinateElement_code]
    exact H.mul_mem ((mem_s _).mp ha) ((mem_s _).mp hb)
  obtain ⟨i, hi⟩ := search s hs hzero hm
  refine ⟨i, (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm⟩
  · rw [node_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    have hj := (mem_s _).mp (hi j)
    rwa [hc] at hj
  · rw [hH, node_card]
end ReeTwo.TailQuotient.Order16Nodes
