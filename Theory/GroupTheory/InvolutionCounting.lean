module

public import Theory.GroupTheory.PGroup.Omega

/-!
# Counting involutions against an elementary subgroup

An elementary binary subgroup contributes one involution for each of its
nonidentity elements. If this exhausts the ambient involution count, every
involution belongs to the subgroup. A central elementary four therefore
forces involution centrality as soon as there are at most three involutions.

This elementary counting step is used after the Sylow alternatives in
Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3 and Lemma 5.1, pp.386, 393.
It does not assume a bound on elementary subgroups or on normal subgroups.
-/

namespace Subgroup

/-- The nonidentity elements of an elementary subgroup exhaust the involutions
whenever their number bounds the total number of involutions from above. -/
public theorem involution_mem_of_card_le
    {P : Type*} [Group P] [Finite P]
    (E : Subgroup P) [IsElementaryAbelian 2 E]
    (hcount : Nat.card {x : P // orderOf x = 2} ≤ Nat.card E - 1)
    {x : P} (hx : orderOf x = 2) : x ∈ E := by
  classical
  let : Fintype E := Fintype.ofFinite E
  let f : {z : E // z ≠ 1} → {z : P // orderOf z = 2} := fun z =>
    ⟨z.val, orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian z.val.val z.val.property)
      (fun h => z.property (Subtype.ext h))⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {z : P // orderOf z = 2} => z.val) h
  have hcard : Nat.card {z : E // z ≠ 1} = Nat.card E - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨z, hz⟩ := (hf.bijective_of_nat_card_le (by omega)).2 ⟨x, hx⟩
  have he : (z.val : P) = x := congrArg Subtype.val hz
  exact he ▸ z.val.property

/-- At most three involutions, in the presence of a central omega four,
forces all involutions to be central. -/
public theorem involutions_central_of_card_le_three_of_omega_center_four
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hcount : Nat.card {x : P // orderOf x = 2} ≤ 3) :
    ∀ x : P, orderOf x = 2 → x ∈ center P := by
  let O := omega₁ (center P) (p := 2)
  let E := O.map (center P).subtype
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hE : Nat.card E = 4 := by
    rw [card_map_of_injective (center P).subtype_injective]
    exact hZ
  intro x hx
  exact map_subtype_le O (involution_mem_of_card_le E (by omega) hx)

end Subgroup
