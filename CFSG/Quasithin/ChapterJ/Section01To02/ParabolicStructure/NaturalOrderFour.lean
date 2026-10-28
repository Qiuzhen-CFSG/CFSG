module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer
public import Theory.LinearAlgebra.OrderFourFixedLine

/-!
# Order-four actors on the original natural section

The natural S₅ action is faithful and has no binary rank-one displacement.
An order-four actor therefore has a one-dimensional fixed space on U/Z.
The general nilpotent-kernel calculation is applied to the original action,
then specialized to the original quotient map H → H/Q ≃ S₅.

This is the fixed-line input used to identify the second center of the
original Sylow subgroup in the marked parabolic calculation of
Aschbacher–Smith, J.4.5. No parabolic model identification is assumed.
-/

public section
namespace CFSG.Quasithin.ChapterJ
open Representation Subgroup

theorem L2FourAction.order_four_fixed_finrank (r : L2FourAction) (g : S5)
    (hg : orderOf g=4) : Module.finrank (ZMod 2) (r.action g).fixedSubmodule=1 := by
  rw [LinearMap.fixedSubmodule_eq_ker]
  apply LinearMap.order_four_fixed_line SL2FourNatural.finrank_vector
  · rw [←map_pow,←hg,pow_orderOf_eq_one,map_one]
  · intro he
    have hg2 : g^2=1 := r.injective (by simpa only [map_pow,map_one] using he)
    have hd := orderOf_dvd_of_pow_eq_one hg2
    rw [hg] at hd
    norm_num at hd
  · have h := r.no_rank_one (g^2)
    rw [map_pow] at h
    exact h

theorem L2FourAction.order_four_fixed_card (r : L2FourAction) (g : S5)
    (hg : orderOf g=4) : Nat.card {v : FourSpace //r.action g v=v}=2 := by
  have h := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=(r.action g).fixedSubmodule)
  rw [r.order_four_fixed_finrank g hg,Nat.card_zmod,pow_one] at h
  exact h

theorem L2FourAction.action_eq_one_iff (r : L2FourAction) (g : S5) :
    r.action g=1 ↔g=1 := by
  constructor
  · intro he
    exact r.injective (he.trans r.action.map_one.symm)
  · rintro rfl
    exact map_one _

variable {G : Type*} [Group G] [Finite G]

/-- The fixed-line calculation on the literal original H/Q action. -/
theorem TypeRuSetup.natural_order_four_fixed_card (d : TypeRuSetup G) (h : d.H)
    (hh : orderOf (d.ru2.quotientMap h) = 4) :
    Nat.card {v : FourSpace //
      d.ru2.naturalAction.action (d.ru2.quotientMap h) v = v} = 2 :=
  d.ru2.naturalAction.order_four_fixed_card _ hh

/-- Faithfulness identifies the literal natural-action kernel with Q. -/
theorem TypeRuSetup.natural_action_eq_one_iff (d : TypeRuSetup G) (h : d.H) :
    d.ru2.naturalAction.action (d.ru2.quotientMap h) = 1 ↔ (h : G) ∈ d.Q := by
  rw [d.ru2.naturalAction.action_eq_one_iff]
  change h ∈ d.ru2.quotientMap.ker ↔ _
  rw [d.ru2.quotient_kernel]
  rfl

end CFSG.Quasithin.ChapterJ
