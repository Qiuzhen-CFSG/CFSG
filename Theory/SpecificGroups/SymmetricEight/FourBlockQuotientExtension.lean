module

public import Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
public import Theory.GroupTheory.NormalNineSylow

/-!
# Sylow subgroups in index-two extensions of the four-block quotient

The actual four-block quotient has characteristic elementary three-core of
order nine and two-group quotient. In a normal extension of index at most
two, this remains a normal ternary plane. A trivial ambient two-core makes
the Sylow action faithful; a Sylow subgroup of order greater than eight
therefore has the Sylow structure of GL₂(3).

This retains the literal quotient model and its normal embedding, as used
by the terminal paired-quotient argument in Aschbacher--Smith, 15.3.25.
-/

public section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
variable {H : Type*} [Group H] [Finite H]

/-- The exact Sylow extension needed for the paired local quotient, with
the normal four-block quotient and its index preserved. -/
theorem sylow_equiv_GL2_three
    (N : Subgroup H) [N.Normal] (hN : N.index ∣ 2)
    (hO : pCore 2 H = ⊥)
    (eN : N ≃* (A6ShadowTwoLocals.fourStabilizer ⧸
      pCore 2 A6ShadowTwoLocals.fourStabilizer))
    (P : Sylow 2 H) (hP : 8 < Nat.card P) :
    ∃ Q : Sylow 2 (GL (Fin 2) (ZMod 3)), Nonempty (P ≃* Q) := by
  let e₃ := (eN.subgroupMap (pCore 3 N)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 3 eN))
  let := threeCore_elementary
  let : IsElementaryAbelian 3 (pCore 3 N) :=
    IsElementaryAbelian.of_injective e₃.toMonoidHom e₃.injective
  have hc : Nat.card (pCore 3 N) = 9 :=
    (Nat.card_congr e₃.toEquiv).trans threeCore_card
  have hq : IsPGroup 2 (N ⧸ pCore 3 N) :=
    threeCore_quotient_two.of_equiv
      (QuotientGroup.congr _ _ eN (pCore_map_iso 3 eN)).symm
  exact Theory.GroupTheory.NormalNineSylow.sylow_equiv_of_index_two_nine_core
    N hN hc hq hO P hP

end Theory.SpecificGroups.SymmetricEight.FourBlockQuotient
