module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Orders
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Fixed B.4 actor comparisons and the equal-order exception

Order comparison eliminates A₆, A₇, SL₅(2), G₂(2)' and M₂₂ for each
terminal component, and SL₄(2) for M₂₃ and J₂. The sole remaining fixed
comparison is a genuine potential equivalence PSL₃(4) ≃ SL₄(2): both
orders are 20160, so order arithmetic cannot exclude it.

Source application: Aschbacher–Smith, B.4.2/B.4.5 and terminal §13.6,
printed pp.86–87 and 935 (1 March 2004 manuscript).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications

private theorem card_linearFourTwo : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  have hp := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.reduceGcd,
    Nat.sub_zero, mul_one, Fin.prod_univ_zero] at hp
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
  rw [Atlas.ExceptionalSupport.card_sl_center] at hc
  norm_num only [Nat.card_zmod, Fintype.card_fin, Nat.reduceSub, Nat.reduceGcd, mul_one] at hc
  exact hc.trans hp

private theorem card_linearFiveTwo : Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have hp := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd, Nat.reduceGcd,
    Nat.sub_zero, mul_one, Fin.prod_univ_zero] at hp
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
  rw [Atlas.ExceptionalSupport.card_sl_center] at hc
  norm_num only [Nat.card_zmod, Fintype.card_fin, Nat.reduceSub, Nat.reduceGcd, mul_one] at hc
  exact hc.trans hp

private theorem card_alternatingSix : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num

private theorem card_alternatingSeven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num

private theorem card_g2DerivedTwo :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

/-- Every fixed competing actor except SL₄(2) is excluded by actual orders. -/
theorem linearFourTwo_of_exceptional_fixed {L : Type*} [Group L]
    (hm : ExceptionalModel L) (hf : FixedCompetitor L) :
    Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  have hc := exceptional_card hm
  cases hf with
  | alternatingSix e =>
    have he := (Nat.card_congr e.toEquiv).trans card_alternatingSix
    omega
  | alternatingSeven e =>
    have he := (Nat.card_congr e.toEquiv).trans card_alternatingSeven
    omega
  | linearFourTwo e => exact ⟨e⟩
  | linearFiveTwo e =>
    have he := (Nat.card_congr e.toEquiv).trans card_linearFiveTwo
    omega
  | g2DerivedTwo e =>
    have he := (Nat.card_congr e.toEquiv).trans card_g2DerivedTwo
    omega
  | mathieuTwentyTwo e =>
    have he := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m22_order
    omega

/-- The sole unresolved fixed comparison is between the two distinct
order-20160 models. This theorem does not identify them. -/
theorem order20160_collision_of_exceptional_fixed {L : Type*} [Group L]
    (hm : ExceptionalModel L) (hf : FixedCompetitor L) :
    Nonempty (Components.L3Four ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨f⟩ := linearFourTwo_of_exceptional_fixed hm hf
  have hc := (Nat.card_congr f.toEquiv).trans card_linearFourTwo
  rcases hm with hm | hm | hm
  all_goals obtain ⟨e⟩ := hm
  · exact ⟨e.symm.trans f⟩
  · have he := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m23_order
    omega
  · have he := (Nat.card_congr e.toEquiv).trans
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier
    omega

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
