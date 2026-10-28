module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.Models

/-!
# Source parameters and the alternating-six covering convention

All incoming field degrees are positive. The actual component-centre
identity excludes the centre-three alternative before converting its
central-quotient marking into an isomorphism of the original component.
The transposition action is still part of the incoming source model;
this reduction does not classify its two-local overgroups.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
1.1.5(3)(c), printed pp.501--502, and 15.3.43, p.1140.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

theorem SimpleModel.positive {H : Type*} [Group H] {n : ℕ}
    (h : SimpleModel H n) : 0 < n := by
  cases h with
  | linearTwo hn _ => omega
  | unitaryThree hn _ => omega
  | binaryLinear hn _ _ _ => omega
  | rankTwo h =>
    cases h with
    | linear hn _ => omega
    | symplectic hn _ => omega
    | g2 hn _ => omega
    | triality hn _ => omega
    | ree_f4 m hm hn _ => omega
    | symplectic_derived hn _ => omega
    | g2_derived hn _ => omega
    | tits hn _ => omega

theorem Model.positive {G : Type*} [Group G] {L : Subgroup G} {z : G} {n : ℕ}
    (h : Model L z n) : 0 < n := by
  cases h with
  | simple _ hm _ => exact hm.positive
  | linearThreeCover hn _ _ _ => omega
  | g2Cover hn _ _ _ => omega
  | alternatingSix hn _ _ => omega

/-- The A₆ source alternative becomes an actual A₆ component only after
the two-group centre condition has excluded the triple cover. -/
theorem alternating_six_of_source_center {G : Type*} [Group G] [Finite G]
    {Yplus S M I L V₁ V₂ : Subgroup G}
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {z : G}
    (hc : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3)
    (ha : ActsTransposition L z) : Nonempty (L ≃* alternatingGroup (Fin 6)) := by
  have hc1 := hc.resolve_right (center_card_ne_three c)
  have hz : center L = ⊥ := Subgroup.card_eq_one.mp hc1
  obtain ⟨e, _, _, _⟩ := ha
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).symm.trans e⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
