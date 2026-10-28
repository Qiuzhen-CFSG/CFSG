module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLowerBound
public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLargeIntersection

/-!
# Local alternatives for the chosen centralizer

Write H=C_G(z), J=O₂(H), K for its ambient image, E for the ambient
derived core, S=C_H(a), and Z for the ambient center of S. The derived
intersection E ∩ Z has order two, four, or eight. Order eight forces
index two over K and an abelian image of S modulo E. Consequently the
desired local alternative is equivalent to the lower bound |E ∩ Z| ≥ 4.

The index-two branch is unconditional. In the covering branch the existing
lower-bound reduction leaves one precise obstruction: an actor of actual
order eight in S with quotient order four, two fixed points on E, and
fourth power a or az. The final theorem records that obstruction alongside
the desired alternatives; it does not assume an order for an actual lift
from its quotient order. The unconditional covering lower bound remains
to be proved.

Only the original local hypotheses and the supplied witnesses occur here.
Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and p.676, the paragraph beginning “We claim that Z(S)”.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The lower bound is the only remaining input to the local alternatives. -/
public theorem chosen_center_local_alternatives_of_lower_bound
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    4 ≤ Nat.card (E ⊓ Z : Subgroup G) →
      Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
        (K.relIndex S ≤ 2 ∧ (commutator S).map S.subtype ≤ E) := by
  intro H J K E S Z hlower
  rcases d.chosen_center_derived_card_cases h with htwo | hfour | height
  · change Nat.card (E ⊓ Z : Subgroup G) = 2 at htwo
    omega
  · exact Or.inl hfour
  · exact Or.inr ⟨(d.chosen_core_relIndex_eq_two_of_center_derived_card_ge_eight
      h height.ge).le, d.chosen_large_center_commutator_le h height⟩

/-- The local alternative and the derived-center lower bound are equivalent
under the original local hypotheses, with no fusion input. -/
public theorem chosen_center_local_alternatives_iff_lower_bound
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    (Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
      (K.relIndex S ≤ 2 ∧ (commutator S).map S.subtype ≤ E)) ↔
        4 ≤ Nat.card (E ⊓ Z : Subgroup G) := by
  intro H J K E S Z
  constructor
  · rintro (hfour | ⟨hindex, _⟩)
    · exact hfour.ge
    · have hindexTwo : K.relIndex S = 2 := Nat.le_antisymm hindex
        (d.chosen_core_relIndex_bounds h).1
      exact d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hindexTwo
  · exact d.chosen_center_local_alternatives_of_lower_bound h

/-- The local alternatives hold whenever the chosen centralizer covers only
the subgroup of order two modulo the core. -/
public theorem chosen_center_local_alternatives_of_core_relIndex_two
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    K.relIndex S = 2 →
      Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
        (K.relIndex S ≤ 2 ∧ (commutator S).map S.subtype ≤ E) := by
  intro H J K E S Z hindex
  exact d.chosen_center_local_alternatives_of_lower_bound h
    (d.chosen_center_derived_card_ge_four_of_core_relIndex_two h hindex)

/-- Every failure of the desired alternatives has the specified order-eight
root obstruction, for the original involution and the same actual actor. -/
public theorem chosen_center_local_alternatives_or_order_eight_root
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let K := J.map H.subtype
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    let Z := (center S).map S.subtype
    (Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
      (K.relIndex S ≤ 2 ∧ (commutator S).map S.subtype ≤ E)) ∨
      (Nat.card (E ⊓ Z : Subgroup G) = 2 ∧ K.relIndex S = 4 ∧
        ∃ y : H, (y : G) ∈ S ∧ orderOf (QuotientGroup.mk' J y) = 4 ∧
          orderOf y = 8 ∧
          Nat.card (E ⊓ centralizer ({(y : G)} : Set G) : Subgroup G) = 2 ∧
          ((y : G) ^ 4 = (d.a : G) ∨ (y : G) ^ 4 = (d.a : G) * z)) := by
  intro H J K E S Z
  by_cases hlower : 4 ≤ Nat.card (E ⊓ Z : Subgroup G)
  · exact Or.inl (d.chosen_center_local_alternatives_of_lower_bound h hlower)
  · have hsmall : Nat.card (E ⊓ Z : Subgroup G) < 4 := Nat.not_le.mp hlower
    have hcases := d.chosen_center_derived_card_cases h
    change Nat.card (E ⊓ Z : Subgroup G) = 2 ∨
      Nat.card (E ⊓ Z : Subgroup G) = 4 ∨
      Nat.card (E ⊓ Z : Subgroup G) = 8 at hcases
    exact Or.inr ⟨by omega, d.chosen_center_small_exists_order_eight_root h hsmall⟩

end Stellmacher.Recognition.ParrottSecondElementaryData
