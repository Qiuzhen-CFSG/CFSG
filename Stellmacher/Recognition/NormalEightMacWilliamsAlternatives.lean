module

public import Theory.SpecificGroups.MacWilliams.SylowPresentations
public import Theory.GroupTheory.PGroup.Omega
public import Theory.SpecificGroups.MacWilliams.HallJankoCenter
public import Theory.SpecificGroups.MacWilliams.UnitaryInvolutions
public import Stellmacher.Recognition.NormalEightMacWilliamsRecognition

/-!
# Assembly of the MacWilliams Sylow alternatives

A Sylow subgroup with central omega of order four cannot be isomorphic to a
model with center of order two. Thus recognition into the two presentations
in `MacWilliamsSylow` reduces the desired involution bound to the unitary
model's count. This route needs only the Hall–Janko model's center calculation,
not the ambient Gorenstein–Harada recognition theorem.

The recognition theorem and the certified model calculations discharge all
inputs of the assembly lemma. In the central-four case this gives exactly
three involutions, hence the first branch of the required dichotomy without
an N₂ hypothesis.

Source: MacWilliams, Trans. AMS 150 (1970), as quoted in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3, p.386, and Lemma 5.1, p.393.
-/

namespace Stellmacher.Recognition.NormalEightCentralFour

open Subgroup MacWilliamsSylow

/-- Recognition into the two concrete presentations, together with the two
model calculations, gives exactly three involutions. The central omega four
excludes the Hall–Janko presentation by its center order. -/
public theorem card_involutions_eq_three_of_sylow_models
    {P : Type*} [Group P] [Finite P]
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (hmodels : Nonempty (P ≃* HallJankoSylow) ∨ Nonempty (P ≃* UnitarySylow))
    (hHall : Nat.card (center HallJankoSylow) = 2)
    (hUnitary : Nat.card {x : UnitarySylow // orderOf x = 2} = 3) :
    Nat.card {x : P // orderOf x = 2} = 3 := by
  rcases hmodels with hmodels | hmodels
  · obtain ⟨e⟩ := hmodels
    have hcenter : Nat.card (center P) = 2 :=
      (Nat.card_congr (Subgroup.centerCongr e).toEquiv).trans hHall
    have hle := card_le_card_group (omega₁ (center P) (p := 2))
    omega
  · obtain ⟨e⟩ := hmodels
    let eI : {x : P // orderOf x = 2} ≃ {x : UnitarySylow // orderOf x = 2} :=
      Equiv.subtypeEquiv e.toEquiv (fun x => by
        change orderOf x = 2 ↔ orderOf (e x) = 2
        rw [e.orderOf_eq])
    exact (Nat.card_congr eI).trans hUnitary

/-- The central-four MacWilliams hypotheses give exactly three Sylow
involutions: the Hall–Janko model is excluded by its center order. -/
public theorem card_involutions_eq_three_of_normalizer_ne
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nat.card {x : S // orderOf x = 2} = 3 :=
  card_involutions_eq_three_of_sylow_models hZ
    (NormalEightMacWilliamsRecognition.sylow_presentation_dichotomy
      hns S hnonab hZ hno W hW hnorm)
    hallJankoSylow_center_card unitarySylow_involution_count

/-- The MacWilliams alternative needed by the normal-eight argument, with
no assumption on solvability of ambient involution centralizers. -/
public theorem macwilliams_alternatives_of_normalizer_ne
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G)) :
    Nat.card {x : S // orderOf x = 2} ≤ 3 ∨
      ∃ z : G, orderOf z = 2 ∧ ¬ Group.IsSolvable (centralizer ({z} : Set G)) :=
  Or.inl (le_of_eq
    (card_involutions_eq_three_of_normalizer_ne hns S hnonab hZ hno W hW hnorm))

end Stellmacher.Recognition.NormalEightCentralFour
