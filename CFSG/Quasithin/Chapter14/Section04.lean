module

public import Theory.ElementaryAbelian.ExtraspecialCardBound
public import CFSG.Quasithin.Chapter14.Section04.CaseOneGeometry
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Consumer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Consumer

/-!
# The numerical extraspecial reductions in §14.4

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §14.4, printed pp. 1005--1012.  The recognition
steps in this section use the local list from §14.3 and the (G_2(3)), (HS),
and (L_4(2)) recognition theorems.  Those interfaces are owned by the
corresponding chapter tasks.  This file records two source-faithful pieces of
the argument that are independent of those recognitions:

* the rank balance in Lemma 14.4.1; and
* the elementary-subgroup bound for the extraspecial 2-groups occurring in
  Lemmas 14.4.2 and 14.4.7.

The latter is an immediate application of the reusable commutator-pairing
bound `extraspecial_two_elementary_card_sq_le`.  It keeps the ambient
extraspecial group and the center-containment hypothesis explicit, so it can
be instantiated for either the (d=4) branch or the (d>4) elimination.
-/

namespace CFSG.Quasithin.Chapter14.Section04

/-! ### Lemma 14.4.1: the rank balance -/

/-- The numerical content of Lemma 14.4.1.  Here `d` is the binary dimension
of the extraspecial quotient, `mE` is the rank of `E`, and `mW` is the rank of
the conjugate fixed layer.  The source has `mE = d / 2` and
`mE + mW = d - 1`; evenness of `d` is the convention that identifies the
quotient dimension with twice its half-rank. -/
public theorem lemma_14_4_1_rank_balance
    (d mE mW : ℕ) (hd_even : d % 2 = 0) (hd_pos : 0 < d)
    (hmE : mE = d / 2) (hbalance : mE + mW = d - 1) :
    mW = d / 2 - 1 := by
  omega

/-- In the (d=4) branch of Lemma 14.4.2 the two ranks are respectively two
and one.  This is often the form needed when passing to the order of the
fixed layers. -/
public theorem lemma_14_4_2_d4_rank_balance
    (mE mW : ℕ) (hmE : mE = 4 / 2) (hbalance : mE + mW = 4 - 1) :
    mE = 2 ∧ mW = 1 := by
  omega

/-! ### The extraspecial elementary-subgroup bound -/

/-- Every center-containing elementary abelian subgroup of an extraspecial
2-group of order (32) has order at most (8).  The proof is the pairing
estimate ( |E|^2 \le 2|Y| ) followed by arithmetic. -/
public theorem extraspecial_order_32_elementary_card_le_eight
    {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial 2 Y]
    (E : Subgroup Y) [IsElementaryAbelian 2 E]
    (hcardY : Nat.card Y = 32) (hZE : Subgroup.center Y ≤ E) :
    Nat.card E ≤ 8 := by
  have hsq := extraspecial_two_elementary_card_sq_le E hZE
  rw [hcardY] at hsq
  nlinarith

/-- Every center-containing elementary abelian subgroup of an extraspecial
2-group of order (512) has order at most (32).  This is the bound used in
the large-(d) cases of Lemma 14.4.2. -/
public theorem extraspecial_order_512_elementary_card_le_thirty_two
    {Y : Type*} [Group Y] [Finite Y] [IsExtraspecial 2 Y]
    (E : Subgroup Y) [IsElementaryAbelian 2 E]
    (hcardY : Nat.card Y = 512) (hZE : Subgroup.center Y ≤ E) :
    Nat.card E ≤ 32 := by
  have hsq := extraspecial_two_elementary_card_sq_le E hZE
  rw [hcardY] at hsq
  nlinarith

end CFSG.Quasithin.Chapter14.Section04
