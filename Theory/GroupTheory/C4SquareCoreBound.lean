module
public import Theory.GroupTheory.PGroup.RankTwoHomocyclicFrattini
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# A self-centralizing homocyclic core of order sixteen

The full group modulo its core acts faithfully on the core's Frattini quotient.
That quotient is a four-group, whose automorphism group has order six.
Thus the original group has order at most 96. No solvability assumption
or restriction to a preselected subgroup of the full group is needed.

This is the full-endpoint bound in the binary case of DGS (10.9),
Groups and Graphs (1985), printed p.163.
-/

open Subgroup
namespace Theory.GroupTheory
public theorem card_le_ninety_six_of_c4_square_core {H : Type*} [Group H] [Finite H]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (e : pCore 2 H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) :
    Nat.card H ≤ 96 := by
  let Q := pCore 2 H
  let V := Q ⧸ frattini Q
  let : IsKleinFour V := isKleinFour_frattini_quotient_of_equiv_prod_zmod (n := 2) (by decide) e
  let a : H →* MulAut V := (quotientAut (frattini Q)).comp MulAut.conjNormal
  have hk : a.ker = Q := pCore_frattini_action_kernel 2 hc
  have hi : Q.index ≤ 6 := by
    rw [←hk,index_ker]
    exact (Nat.card_le_card_of_injective a.range.subtype a.range.subtype_injective).trans_eq
      (IsKleinFour.card_mulAut V)
  have hQ : Nat.card Q = 16 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num
  have hh := Q.card_mul_index
  rw [hQ] at hh
  omega

end Theory.GroupTheory
