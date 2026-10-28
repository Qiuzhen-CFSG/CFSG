module

public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The outer groups of the cubic block models

The faithful inner action has order 12 for A₄ and 144 for A₄². The actual
full automorphism equivalences give orders 24 and 1152, so the outer
quotients have orders two and eight. These are precisely the Sylow
supplementation inputs in Aschbacher--Smith 14.1.10, printed p.978.
-/

public section
open Subgroup
namespace AlternatingFourPair

/-- The outer group of the actual A₄ model has order two. -/
theorem card_outer_single : Nat.card (MulAut.Outer A) = 2 := by
  have hc : Nat.card (MulAut.innerSubgroup A) = 12 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot
        (alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4))))).toEquiv]
    exact alternatingGroup.card_of_card_eq_four (by norm_num)
  have ha : Nat.card (MulAut A) = 24 := by
    rw [←Nat.card_congr eA.toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hi := (MulAut.innerSubgroup A).index_mul_card
  rw [hc,ha] at hi
  change (MulAut.innerSubgroup A).index = 2
  omega

/-- The outer group of the actual pair A₄² has order eight. -/
theorem card_outer_pair : Nat.card (MulAut.Outer Model) = 8 := by
  have hc : Nat.card (MulAut.innerSubgroup Model) = 144 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).toEquiv]
    change Nat.card (A × A) = 144
    rw [Nat.card_prod,alternatingGroup.card_of_card_eq_four (by norm_num)]
  have ha : Nat.card (MulAut Model) = 1152 :=
    (Nat.card_congr mulAut_equiv_regularWreath.toEquiv).trans symmetric_wreath_card
  have hi := (MulAut.innerSubgroup Model).index_mul_card
  rw [hc,ha] at hi
  change (MulAut.innerSubgroup Model).index = 8
  omega

/-- Both cubic block models have two-group outer automorphism groups. -/
theorem outer_single_two : IsPGroup 2 (MulAut.Outer A) :=
  IsPGroup.of_card (n := 1) (by simpa using card_outer_single)

theorem outer_pair_two : IsPGroup 2 (MulAut.Outer Model) :=
  IsPGroup.of_card (n := 3) (by simpa using card_outer_pair)

end AlternatingFourPair
