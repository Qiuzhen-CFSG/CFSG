module

public import Theory.Representation.FourSmallThreeInversion
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.PGroup.ClassTwoFixedFrattiniRank
public import Theory.GroupTheory.QuasithinBasic

/-!
# A four-group inverter on the actual supercritical Frattini quotient

A supercritical subgroup of a rank-two three-group has exponent three
and class at most two. The generator bound and Burnside's basis theorem
put its elementary Frattini quotient at order at most nine. Coprime
faithfulness survives the actual restriction and quotient homomorphisms,
so the small elementary action theorem supplies a nonidentity inverter.

Source: Aschbacher--Smith A.1.31(3), printed p.27; this is the specified
supercritical action used in the three-section reducibility argument.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace IsSupercriticalPSubgroup
variable {P A : Type*} [Group P] [Finite P] [Group A] [Finite A]
  [IsElementaryAbelian 2 A] {X : Subgroup P}

/-- The faithful four-group action on P has an inverter on the actual
supercritical Frattini quotient. -/
theorem exists_frattini_inverter
    (hX : IsSupercriticalPSubgroup 3 X) (hP : IsPGroup 3 P)
    (hr : primeRank 3 P ≤ 2) (action : A →* MulAut P)
    (hfaith : Function.Injective action) (hA : Nat.card A = 4) :
    letI : X.Characteristic := hX.characteristic
    ∃ a : A, a ≠ 1 ∧ ∀ w : X ⧸ frattini X,
      quotientAut (frattini X) (MulAut.characteristic X (action a)) w = w⁻¹ := by
  let : X.Characteristic := hX.characteristic
  let : Fact (IsPGroup 3 X) := ⟨hP.to_subgroup X⟩
  let : IsElementaryAbelian 3 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  have hrX : Group.rank X ≤ 2 :=
    (hP.to_subgroup X).rank_le_two_of_exponent_prime_class_two (by decide)
      hX.pow_eq_one hX.derived_le_center ((Theory.GroupTheory.primeRank_le_of_injective 3 X.subtype X.subtype_injective).trans hr)
  have hrW : Group.rank (X ⧸ frattini X) ≤ 2 := by
    rw [← Group.rank_eq_rank_quotient_frattini X]
    exact hrX
  have hW : Nat.card (X ⧸ frattini X) ≤ 9 := by
    have hd := card_dvd_exponent_pow_rank' (X ⧸ frattini X)
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 (X ⧸ frattini X)))
    exact (Nat.le_of_dvd (by positivity) hd).trans
      (Nat.pow_le_pow_right (by decide : 0 < 3) hrW)
  exact Representation.exists_inversion_of_elementary_card_four_card_le_nine
    (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp action)
    (hX.injective_frattini_action_of_coprime hP (by decide) action hfaith
      (by rw [hA]; decide)) hA hW
end IsSupercriticalPSubgroup

