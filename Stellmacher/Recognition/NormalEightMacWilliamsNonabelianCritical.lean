module

public import Theory.GroupTheory.PGroup.NormalEightCriticalExtension
public import Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCenter

/-!
# The nonabelian critical-subgroup extension step

For a Sylow two-subgroup with central first omega of order four and no
normal elementary eight, the ambient simplicity and nontrivial normalizer
action force the center of a nonabelian critical subgroup to be elementary.
The intrinsic extension theorem then makes every Sylow involution central:
the three-subgroups lemma puts ambient commutators in the critical center,
and the normal-eight obstruction rules out a noncentral involution.

The alternative reduction from central-involution fusion is retained:
Burnside fusion and characteristic restriction give transitivity on the
critical subgroup's three involutions, which also suffices for the intrinsic
extension theorem. Neither route assumes an ambient elementary-rank bound.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, p.386, quoting
MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCritical

open Subgroup

/-- In the nonabelian critical-subgroup case, the ambient normalizer hypothesis
forces every Sylow involution to be central. -/
public theorem involutions_central_of_nonabelian_critical
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) (hCnonab : ¬ IsMulCommutative C) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  let : IsElementaryAbelian 2 (center C) :=
    NormalEightMacWilliamsNonabelianCenter.elementary_center_of_nonabelian_critical
      hns S hno hZ hnorm hC hCnonab
  intro x hx
  exact hC.involutions_central_of_elementary_center hno hZ x
    (by simpa only [hx] using pow_orderOf_eq_one x)

/-- Central-involution fusion completes the nonabelian critical extension argument. -/
public theorem involutions_central_of_central_fusion
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) (hCnonab : ¬ IsMulCommutative C)
    (hfuse : ∀ x y : S, x ∈ center S → y ∈ center S →
      orderOf x = 2 → orderOf y = 2 → IsConj (x : G) (y : G)) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  have htrans := S.critical_involutions_transitive_of_central_fusion hno hZ hC hfuse
  intro x hx
  exact hC.involutions_central_of_transitive_involutions S.isPGroup' hno hZ hCnonab
    htrans x (by simpa only [hx] using pow_orderOf_eq_one x)

end Stellmacher.Recognition.NormalEightMacWilliamsNonabelianCritical
