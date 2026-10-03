module

public import Theory.Frattini.PGroupMap
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini

/-!
# Bounding a Frattini quotient using a subgroup

For a subgroup `A` of a finite two-group `P`, functoriality embeds the image
of `Φ(A)` in `Φ(P)`. Comparing orders gives
`|P/Φ(P)| ≤ [P:A] |A/Φ(A)|`. If `A` is abelian, its Frattini quotient has
the same order as its first omega subgroup.

This elementary generator-count comparison is used in the normal-subgroup
specialization of MacWilliams–Sah, quoted in Janko–Thompson,
Math. Z. 113 (1970), result 1.1, printed p.385.
-/

open Subgroup

namespace IsPGroup

/-- A subgroup bounds the ambient Frattini quotient by its index times its
own Frattini quotient order. -/
public theorem card_frattini_quotient_le_subgroup_index_mul
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) :
    Nat.card (P ⧸ frattini P) ≤ A.index * Nat.card (A ⧸ frattini A) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Fact (IsPGroup 2 A) := ⟨hP.to_subgroup A⟩
  have hle := card_le_of_le (frattini_map_le_of_isPGroup (p := 2) A.subtype)
  rw [card_map_of_injective A.subtype_injective] at hle
  have hPcard := card_eq_card_quotient_mul_card_subgroup (frattini P)
  have hAcard := card_eq_card_quotient_mul_card_subgroup (frattini A)
  have hindex := A.card_mul_index
  have hpos := Nat.card_pos (α := frattini A)
  have hm := Nat.mul_le_mul_left (Nat.card (P ⧸ frattini P)) hle
  rw [← hPcard, ← hindex, hAcard] at hm
  nlinarith

/-- For an abelian subgroup, replace its Frattini quotient order by its omega order. -/
public theorem card_frattini_quotient_le_index_mul_omega_one
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [IsMulCommutative A] :
    Nat.card (P ⧸ frattini P) ≤ A.index * Nat.card (omega₁ A (p := 2)) := by
  simpa only [(hP.to_subgroup A).card_frattini_quotient_eq_card_omega_one]
    using hP.card_frattini_quotient_le_subgroup_index_mul A

end IsPGroup
