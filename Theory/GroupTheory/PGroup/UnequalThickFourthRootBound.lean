module

public import Theory.GroupTheory.PGroup.OmegaAction
public import Theory.GroupTheory.PGroup.NormalEightInvolutionLift
public import Theory.GroupTheory.PGroup.NormalEightCentralAction
public import Theory.GroupTheory.PGroup.UnequalCyclicFourRootBound
public import Theory.GroupTheory.PGroup.HomocyclicElementaryFourTorsion

/-!
# Fourth-root actions for unequal cyclic factors

When both cyclic factors of a normal abelian subgroup have order at least
eight, restriction to its characteristic eighth-root subgroup reduces the
fourth-root image bound to the corresponding faithful action bound for
`C₈ × C₈`. The no-normal-eight hypothesis supplies pointwise fixation of
involutions. A complement to the restriction kernel handles faithfulness.

The homocyclic counting result is an explicit premise of the reduction below.
The separate case with smaller factor `C₄` still requires the structural
normal elementary eight obstruction; a congruence calculation alone does
not give its desired bound.

Source: the normal abelian reductions in MacWilliams, *On 2-groups with no
normal abelian subgroups of rank 3*, Trans. AMS 150 (1970), §1.2.
-/

open Subgroup OmegaAction

universe u

/-- Reduce factors of order at least eight to the faithful homocyclic count. -/
public theorem IsPGroup.card_omegaTwo_image_le_four_of_homocyclic_eight_bound
    {P : Type u} [Group P] [Finite P]
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : Subgroup.centralizer (D : Set P) ≤ D)
    (n m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^m))))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hcount : ∀ (H : Type u) [Group H] [Finite H] [IsMulCommutative H],
      (H ≃* (Multiplicative (ZMod (2^3)) × Multiplicative (ZMod (2^3)))) →
      ∀ B : Subgroup (MulAut H), IsElementaryAbelian 2 B →
        (∀ a ∈ B, ∀ x : H, x^2=1 → a x=x) →
        (∀ a ∈ B, (∀ x : H, x^4=1 → a x=x) → a=1) → Nat.card B ≤ 4) :
    Nat.card ((Subgroup.omegaTwoConjugation D).comp A.subtype).range ≤ 4 := by
  let ρ := (MulAut.conjNormal : P →* MulAut D).comp A.subtype
  change Nat.card ((omegaRestriction D 2 2).comp ρ).range ≤ 4
  rw [card_fourth_root_range_eq_on_eighth_roots]
  apply card_restriction_range_le_of_faithful_bound
  · intro a x hx
    apply Subtype.ext
    exact IsPGroup.conjNormal_fixed_of_square_eq_one_of_no_normal_eight
      hno hZ D hD a x (congrArg Subtype.val hx)
  · exact hcount _ ((e.omega 2 3).trans (productOmegaEquiv n m 3 (hm.trans hmn) hm))

/-- Bound the fourth-root action for every unequal pair of cyclic factors of
order at least four.  The smaller factor of order four is handled by the
intrinsic norm-control calculation; for larger factors, restriction to the
eighth-root subgroup reduces to the homocyclic count. -/
public theorem IsPGroup.card_omegaTwo_image_le_four_of_unequal_thick_factors
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup 2 P)
    (hno : ¬ ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (Subgroup.center P) (p := 2)) = 4)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hD : Subgroup.centralizer (D : Set P) ≤ D)
    (n m : ℕ) (hm : 2 ≤ m) (hmn : m < n)
    (e : D ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^m))))
    (A : Subgroup P) [IsElementaryAbelian 2 A] :
    Nat.card ((Subgroup.omegaTwoConjugation D).comp A.subtype).range ≤ 4 := by
  by_cases hm2 : m = 2
  · subst m
    exact IsPGroup.card_omegaTwo_image_le_four_of_cyclic_four hP hno hZ D hD n
      (by omega) e A
  · have hm3 : 3 ≤ m := by omega
    apply IsPGroup.card_omegaTwo_image_le_four_of_homocyclic_eight_bound
      hno hZ D hD n m hm3 (Nat.le_of_lt hmn) e A
    intro H _ _ _ he B hB hfix hfaith
    let : IsElementaryAbelian 2 B := hB
    exact HomocyclicFourTorsion.card_le_four_of_homocyclic_elementary_four_torsion
      3 (by decide) he B hfix hfaith
