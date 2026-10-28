module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.CriticalCenterExponent
public import Theory.GroupTheory.SylowPGroupAutomizer

/-!
# Elementary critical centers in the central-two exotic branch

The critical center omega four maps onto the unique normal four. Consequently
every critical involution is central in the critical subgroup. The intrinsic
critical-center exponent theorem then makes that center elementary: otherwise
the full automorphism group of the Sylow subgroup would be a two-group,
contrary to its nontrivial outer normalizer action.

This proves the conditional elementary-center step. The choice of the critical
subgroup, and the proof that its center omega has order four, remain with the
consumer. No rank or Sylow-order bound, model recognition, or transitivity
of automorphisms on critical involutions is used.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticCriticalCenterExponent

open Subgroup

/-- The center of a nonabelian critical subgroup whose center omega has order
four is elementary in the central-two outer-normalizer branch. -/
public theorem center_elementary_of_omega_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C)
    (hCnonab : ¬ IsMulCommutative C)
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4) :
    IsElementaryAbelian 2 (center C) := by
  exact hC.center_elementary_of_omega_ambient_center_two_of_not_isPGroup_mulAut
    S.isPGroup' (S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm) hZ
    hCnonab hfour
    (hC.square_one_mem_center_of_unique_four_of_omega_center_four hno W hW hunique hfour)

end Stellmacher.Recognition.NormalEightExoticCriticalCenterExponent
