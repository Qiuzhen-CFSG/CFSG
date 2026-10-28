module

public import Theory.SpecificGroups.PSL3Four.InnerInvolutionCentralizers
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure
public import Theory.GroupAction.InnerCentralizerCardinality

/-!
# No factor of nine in an inner involution centralizer of Aut(PSL₃(4))

The inner part has order 64 and the actual outer quotient has order dividing
12. Thus the full automorphism centralizer has order dividing 768.
Source: Aschbacher--Smith 14.3.20, printed p.998, even-model inspection.
-/

public section
namespace Matrix.PSL3Four
open Subgroup

/-- The full automorphism centralizer of an inner involution has no factor nine. -/
theorem not_nine_dvd_inner_involution_centralizer (x : PSL) (hx : orderOf x = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({MulAut.conj x} : Set (MulAut PSL))) := by
  have hi : Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
    let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
    exact MulAut.conj_injective_of_center_eq_bot
      (Group.IsPerfect.center_quotient_center_eq_bot SL)
  have ha : orderOf (MulAut.conj x) = 2 := (orderOf_injective _ hi x).trans hx
  have hne : MulAut.conj x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    contradiction
  have hsq : (MulAut.conj x) ^ 2 = 1 := by
    simpa only [ha] using pow_orderOf_eq_one (MulAut.conj x)
  have hd := MulAut.centralizer_card_dvd_inner_mul_outer (MulAut.conj x)
  rw [show Nat.card (MulAut.innerSubgroup PSL ⊓
      centralizer ({MulAut.conj x} : Set (MulAut PSL)) : Subgroup (MulAut PSL)) = 64 from
    InnerInvolutionCentralizers.card_innerCentralizer _ ⟨x, rfl⟩ hne hsq] at hd
  have hb : Nat.card (centralizer ({MulAut.conj x} : Set (MulAut PSL))) ∣ 768 :=
    hd.trans (Nat.mul_dvd_mul_left 64 OuterThreeStructure.outer_card_dvd_twelve)
  exact fun hn => (by decide : ¬ 9 ∣ 768) (hn.trans hb)

end Matrix.PSL3Four
