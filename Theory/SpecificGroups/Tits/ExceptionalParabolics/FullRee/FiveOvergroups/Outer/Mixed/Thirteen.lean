module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Outer.Mixed.Semilinear
public import Theory.SpecificGroups.PSL2.TwentyFiveThirteen

/-!
# Thirteen-subgroup geometry in the literal mixed PSL₂(25) extension

The marked native PSL₂ core has index two. The general order-twenty-five
calculation therefore gives the Sylow normalizer of order fifty-two and
all overgroup indices needed for the remaining-point argument. Overgroups
must avoid containing the core; the original J.5.5 action supplies that
separate source condition. No normalizer or subgroup catalogue assumption
is made here.

Source: Aschbacher--Smith J.5.5(5), printed p.447.
-/

public noncomputable section
open Subgroup
namespace Tits.Max4Outer.Mixed
open Max4Projective Theory.PSL2.TwentyFive

theorem plus_card : Nat.card Plus=15600 :=
  IndexTwo.card_group pslCore pslCore_index pslCoreEquiv.symm field_card

instance finitePlus : Finite Plus := Nat.finite_of_card_ne_zero (by rw [plus_card];decide)

theorem sylow_thirteen_card (P : Sylow 13 Plus) : Nat.card P=13 :=
  IndexTwo.sylow_card pslCore pslCore_index pslCoreEquiv.symm field_card P

theorem sylow_thirteen_le_core (P : Sylow 13 Plus) : (P : Subgroup Plus)≤pslCore :=
  IndexTwo.sylow_le pslCore pslCore_index pslCoreEquiv.symm field_card P

theorem sylow_thirteen_normalizer_card (P : Sylow 13 Plus) :
    Nat.card (normalizer (P : Set Plus))=52 :=
  IndexTwo.normalizer_card pslCore pslCore_index pslCoreEquiv.symm field_card P

theorem thirteen_overgroup_card (P : Sylow 13 Plus) (H : Subgroup Plus)
    (hPH : (P : Subgroup Plus)≤H) (hcore : ¬pslCore≤H) :
    Nat.card H=13 ∨ Nat.card H=26 ∨ Nat.card H=52 :=
  IndexTwo.overgroup_card pslCore pslCore_index pslCoreEquiv.symm field_card P H hPH hcore

theorem thirteen_overgroup_index (P : Sylow 13 Plus) (H : Subgroup Plus)
    (hPH : (P : Subgroup Plus)≤H) (hcore : ¬pslCore≤H) :
    H.index=300 ∨ H.index=600 ∨ H.index=1200 :=
  IndexTwo.overgroup_index pslCore pslCore_index pslCoreEquiv.symm field_card P H hPH hcore

theorem thirteen_overgroup_le_normalizer (P : Sylow 13 Plus) (H : Subgroup Plus)
    (hPH : (P : Subgroup Plus)≤H) (hcore : ¬pslCore≤H) :
    H≤normalizer (P : Set Plus) :=
  IndexTwo.overgroup_le_normalizer pslCore pslCore_index pslCoreEquiv.symm field_card P H hPH hcore

theorem thirteen_overgroup_index_mod (P : Sylow 13 Plus) (H : Subgroup Plus)
    (hPH : (P : Subgroup Plus)≤H) (hcore : ¬pslCore≤H) :
    H.index%13=1 ∨ H.index%13=2 ∨ H.index%13=4 := by
  rcases thirteen_overgroup_index P H hPH hcore with h|h|h <;> simp [h]

end Tits.Max4Outer.Mixed
