module

public import Theory.GroupTheory.PGroup.NormalEightInvolutionLift
public import Theory.GroupTheory.PGroup.NormalEightUnequalThickAction
public import Theory.GroupTheory.SpecificGroups.AbelianCyclicTwoFixedAut

/-!
# Elementary action bound for unequal cyclic factors

If the ambient conjugation image on a self-centralizing normal abelian
subgroup is abelian, the no-normal-eight hypothesis makes restriction to
second omega faithful on elementary action images. A bound of four on the
restricted image therefore suffices.

For a product of a cyclic two-group with a factor of order two, the required
abelian-image and restricted-image bounds are automorphism calculations.
When both factors have order at least four, the structural argument in
`NormalEightUnequalThickAction` supplies the bound. Ordering the two exponents
and splitting according to whether the smaller is one combines these cases.

Source: the MacWilliams–Sah bound quoted in Janko–Thompson, Math. Z. 113
(1970), 1.1, printed p.385; MacWilliams, Trans. AMS 150 (1970), §1.2,
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace IsPGroup

/-- A bound on the action on fourth roots gives the full action bound when
the ambient conjugation image is abelian. -/
public theorem card_conj_image_le_four_of_abelian_action
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (hcomm : ∀ g a : P, Commute (MulAut.conjNormal (H := D) g) (MulAut.conjNormal a))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hsmall : Nat.card ((omegaTwoConjugation D).comp A.subtype).range ≤ 4) :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 :=
  (hP.card_conj_image_le_omega_two_image_of_abelian_action hno hZ D hD hcomm A).trans hsmall

/-- Ambient conjugation fixes every involution of a self-centralizing normal
abelian subgroup when the central omega has order four. -/
public theorem conjNormal_apply_eq_self_of_square_eq_one_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (g : P) (d : D) (hd : d ^ 2 = 1) : MulAut.conjNormal g d = d := by
  have hEq := omega_one_normal_abelian_eq_center_of_no_normal_eight hno hZ D hD
  have hz : (d : P) ∈ (omega₁ (center P) (p := 2)).map (center P).subtype := by
    rw [← hEq]
    exact ⟨d, subset_closure (by simpa using hd), rfl⟩
  have hdc : (d : P) ∈ center P := map_subtype_le _ hz
  apply Subtype.ext
  change g * (d : P) * g⁻¹ = d
  rw [mem_center_iff.mp hdc g, mul_inv_cancel_right]

private theorem card_conj_image_le_four_of_cyclic_two_factor
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n : ℕ) (hn : 2 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod 2)))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  have hfix := conjNormal_apply_eq_self_of_square_eq_one_of_no_normal_eight hno hZ D hD
  apply card_conj_image_le_four_of_abelian_action hP hno hZ D hD
    (abelian_cyclic_two_fixed_aut_commute_of_equiv hn e MulAut.conjNormal hfix) A
  simpa only [omegaTwoConjugation, MonoidHom.comp_assoc] using
    abelian_cyclic_two_fixed_aut_omega_two_range_card_le_four_of_equiv hn e
      ((MulAut.conjNormal : P →* MulAut D).comp A.subtype)
      (fun a d hd => hfix a d hd)

/-- An elementary subgroup acts with image of order at most four on a normal
abelian self-centralizing subgroup with two unequal nontrivial cyclic factors,
provided there is no normal elementary eight and the central omega has order four. -/
public theorem card_conj_image_le_four_of_unequal_factors
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : centralizer (D : Set P) ≤ D)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m))))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
  have ordered (n m : ℕ) (hm : 1 ≤ m) (hmn : m < n)
      (e : D ≃* (Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ m)))) :
      Nat.card ((MulAut.conjNormal : P →* MulAut D).comp A.subtype).range ≤ 4 := by
    by_cases hm1 : m = 1
    · subst m
      exact card_conj_image_le_four_of_cyclic_two_factor hP hno hZ D hD n
        (by omega) e A
    · exact card_conj_image_le_four_of_unequal_thick_factors hP hno hZ D hD n m
        (by omega) hmn e A
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact ordered m n hn hlt (e.trans MulEquiv.prodComm)
  · exact ordered n m hm hgt e

end IsPGroup
