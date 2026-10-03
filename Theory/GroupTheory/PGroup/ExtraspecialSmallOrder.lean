module

public import Theory.GroupTheory.PGroup.RankTwoSymplecticBounds
public import Theory.ElementaryAbelian.ExtraspecialCardBound

/-!
# The first two possible extraspecial binary orders

An extraspecial two-group of order below thirty-two has order eight.
For an elementary subgroup, adjoining the center and applying the
commutator-pairing bound gives elementary order below eight. The existing
rank-two classification then gives the result. This uses a rank bound only
for the small group being classified; it imposes none on an ambient group.

This numerical reduction separates arbitrary extraspecial width from the
order-thirty-two case in Janko–Thompson (1970), §4, printed p.389.
-/

open Subgroup

namespace IsExtraspecial

/-- Below order thirty-two, adjoining the center and the pairing bound force
all elementary subgroups of an extraspecial binary group to have order below eight. -/
public theorem elementary_card_lt_eight_of_card_lt_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hsmall : Nat.card P < 32)
    (U : Subgroup P) [IsElementaryAbelian 2 U] : Nat.card U < 8 := by
  let : IsElementaryAbelian 2 (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [center_order_p 2 P] using (pow_card_eq_one' (x := z)) }
  let : IsElementaryAbelian 2 (U ⊔ center P : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (center_le_centralizer _)
  have hsq := extraspecial_two_elementary_card_sq_le (U ⊔ center P) le_sup_right
  have hle := card_le_of_le (show U ≤ U ⊔ center P from le_sup_left)
  nlinarith

/-- An extraspecial binary group of order below thirty-two has order eight. -/
public theorem card_eq_eight_of_card_lt_thirty_two
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hsmall : Nat.card P < 32) : Nat.card P = 8 := by
  have hrank (U : Subgroup P) (hU : IsElementaryAbelian 2 U) : Nat.card U < 8 := by
    let : IsElementaryAbelian 2 U := hU
    exact elementary_card_lt_eight_of_card_lt_thirty_two hsmall U
  exact ((IsRankTwoExtraspecialModel.card_eight_hall_or_thirty_two
    (rank_two_classification hrank)).resolve_right (by omega)).1

/-- This alternative covers every extraspecial width, with no rank hypothesis. -/
public theorem card_eq_eight_or_thirty_two_le
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P] :
    Nat.card P = 8 ∨ 32 ≤ Nat.card P := by
  by_cases h : Nat.card P < 32
  · exact Or.inl (card_eq_eight_of_card_lt_thirty_two h)
  · exact Or.inr (by omega)

end IsExtraspecial
