module
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# An element of order nine in binary SL₂(8)

The odd Sylow subgroups are cyclic by the faithful two-dimensional action.
The order formula gives a Sylow three-subgroup of order nine, whose generator
is the required element. This avoids a new finite-field matrix certificate.
Source: Huppert II.6.14 and the binary PSL₂ row in Aschbacher--Smith 4.3.16, p.618.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SL2

/-- Every field of order eight supplies an order-nine element in SL₂. -/
theorem exists_orderOf_nine {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hc : Nat.card F = 8) : ∃ x : SL(2,F), orderOf x = 9 := by
  let P := Classical.choice (inferInstance : Nonempty (Sylow 3 SL(2,F)))
  have hp : Nat.card P = 9 := by
    rw [P.card_eq_multiplicity,BenderSuzuki.External.huppert614_card_specialLinearGroup,hc]
    decide +kernel
  have hcyc : IsCyclic P := odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide)
    (P : Subgroup SL(2,F)).subtype (P : Subgroup SL(2,F)).subtype_injective
  obtain ⟨x,hx⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hcyc
  exact ⟨x,(Subgroup.orderOf_coe x).trans (hx.trans hp)⟩

end Matrix.SL2
