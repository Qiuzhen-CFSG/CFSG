module

public import CFSG.Quasithin.Chapter1.Section03.Basic
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms

/-!
# The order of the original Xi Frattini quotient

Both groups in Definition 1.3.1 have a Frattini quotient of order p².
The elementary case has trivial Frattini subgroup; the extraspecial case
has Frattini subgroup equal to its center of order p. The result uses the
literal quotient and supplies the rank-two count in Lemma3.2.13.
Source: Aschbacher--Smith, printed pp.507 and584--585.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter1
theorem XiOddQuotient.frattini_card {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} [Fact p.Prime] (h : XiOddQuotient p Q) :
    Nat.card (Q ⧸ frattini Q) = p ^ 2 := by
  rcases h with ⟨he, hc⟩ | ⟨he, hc, _⟩
  · let := he
    let : Fact (IsPGroup p Q) := ⟨IsElementaryAbelian.isPGroup p Q⟩
    rw [Nat.card_congr (frattiniQuotientEquivOfIsElementaryAbelian (R := Q) (p := p)).toEquiv]
    exact hc
  · let := he
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
      (IsExtraspecial.frattini_eq_center (P := Q) (p := p))).toEquiv]
    have hh := card_eq_card_quotient_mul_card_subgroup (center Q)
    rw [hc, IsExtraspecial.center_order_p p Q] at hh
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos
      (hh.symm.trans (by ring : p ^ 3 = p ^ 2 * p))
end CFSG.Quasithin.Chapter1

