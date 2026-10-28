module
public import Stellmacher.SectionOne.NineCoreSupportDecompositionCountingGeometry
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupAction.FourElementTwoAction

/-!
# An invariant three-line is fixed-free on a nonquadratic sixteen-module

For a faithful binary module of order sixteen, an order-three subgroup
normalized by a nonquadratic two-group actor has no nonidentity fixed point.
The actor need not be faithful on any specified summand.

The order-three fixed-space dichotomy leaves orders one and four. In the
latter case coprime action splits the module into two invariant summands
of order four. Every two-group action on four elements is quadratic, so
their generated module is quadratic too, a contradiction.

This supplies the initial-center half of the D* selection in Stellmacher
(9.1), printed p48 of `refs/files/stellmacher-n-group.pdf`. The chosen line
and original action are retained; its lift is handled separately.
-/

namespace Stellmacher.SectionOne
open scoped IsMulCommutative
universe u

public theorem normalized_three_fixed_free_of_nonquadratic_sixteen
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (D J : Subgroup X) (hD : Nat.card D = 3) (hJ : IsPGroup 2 J)
    (hV : Nat.card V = 16) (hfaith : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (hnormal : J ≤ Subgroup.normalizer (D : Set X))
    (hnonquad : commutatorAction₂ J V ≠ ⊥) : FixedPoints.subgroup D V = ⊥ := by
  rcases nineCoreSupportDecomposition_line_fixed_card D hD hV hfaith with hone | hfour
  · exact Subgroup.card_eq_one.mp hone
  exfalso
  apply hnonquad
  let P := FixedPoints.subgroup D V
  let Q := commutatorAction D V
  have hcompl : IsCompl P Q :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := V)).comm a b)
      (by rw [hD, hV]; decide) inferInstance
  have hQcard : Nat.card Q = 4 := by
    have hprod := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint P Q
      Subgroup.le_normalizer_of_normal hcompl.disjoint
    rw [hcompl.sup_eq_top,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv, hV] at hprod
    change Nat.card P = 4 at hfour
    rw [hfour] at hprod
    omega
  have hPinv : IsInvariant J V P := fixedPoints_isInvariant_of_normalizing_actor J D hnormal
  have hQinv : IsInvariant J V Q := commutatorAction_isInvariant_of_normalizing_actor J D hnormal
  let pieces : Bool → Subgroup V := fun b => if b then P else Q
  have hpieces : ∀ b, IsInvariant J V (pieces b) := by
    intro b
    cases b
    · exact hQinv
    · exact hPinv
  have hgen : (⊤ : Subgroup V) = ⨆ b, pieces b := by
    simpa only [iSup_bool_eq, pieces, Bool.false_eq_true, ↓reduceIte, sup_comm] using
      hcompl.sup_eq_top.symm
  apply RankOneThreeGroupAssembly.commutatorAction₂_eq_bot_of_iSup_quadratic pieces hpieces hgen
  intro b
  let _ := hpieces b
  apply two_group_action_on_four_is_quadratic hJ
  cases b
  · exact hQcard
  · exact hfour

end Stellmacher.SectionOne
