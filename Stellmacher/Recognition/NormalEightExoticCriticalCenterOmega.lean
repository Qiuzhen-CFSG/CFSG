module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.UniqueNormalFourCriticalExistence

/-!
# Choosing the critical center omega in the exotic branch

The unique normal elementary four of the Sylow two-subgroup is characteristic.
Extend it to a maximal characteristic abelian subgroup, and take a critical
subgroup having that overgroup as its center. The center omega contains the four
and cannot be larger in the absence of normal elementary eights.

Thus this existence step needs only the intrinsic Sylow hypotheses. The ambient
outer action, fusion, and elementary sixteen are not needed for this choice.
Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386;
the construction is Thompson's critical subgroup theorem, Gorenstein,
*Finite Groups*, Theorem 5.3.11, pp.185–186.
-/

namespace Stellmacher.Recognition.NormalEightExoticCriticalCenterOmega

open Subgroup

/-- Choose a critical subgroup with center omega of order four. -/
public theorem exists_critical_center_omega_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧
      Nat.card (omega₁ (center C) (p := 2)) = 4 :=
  S.isPGroup'.exists_criticalPSubgroup_card_omega_center_four hno W hW hunique

end Stellmacher.Recognition.NormalEightExoticCriticalCenterOmega
