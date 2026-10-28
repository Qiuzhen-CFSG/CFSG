module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.UniqueNormalFourCriticalCenter
public import Theory.GroupTheory.SylowPGroupAutomizer
public import Stellmacher.Recognition.NormalEightExoticCriticalCenterOmega
public import Stellmacher.Recognition.NormalEightExoticCriticalCenterExponent

/-!
# Critical core in the central-two exotic branch

The nontrivial outer normalizer action rules out every abelian critical subgroup.
The center of a critical subgroup has first omega of order two or four. In the
second case that omega maps onto the unique normal four, and all involutions of
the critical subgroup are central in it. If its center is elementary, it therefore
has order four, giving the requested structural core data.

Choose the critical subgroup with center containing the unique normal four.
The center-exponent theorem then makes its center elementary, using the outer
normalizer action and the ambient central omega of order two. This gives the
structural-core witness without a rank bound or an elementary sixteen.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticCriticalCenter

open Subgroup

/-- The outer-action branch has a nonabelian critical subgroup; its central
first omega has order two or four. -/
public theorem exists_nonabelian_critical_subgroup_data
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧ ¬ IsMulCommutative C ∧
      (Nat.card (omega₁ (center C) (p := 2)) = 2 ∨
        Nat.card (omega₁ (center C) (p := 2)) = 4) := by
  obtain ⟨C, hC⟩ := S.isPGroup'.exists_criticalPSubgroup
  have hAut := S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm
  exact ⟨C, hC,
    hC.not_isMulCommutative_of_unique_four_of_omega_center_two
      S.isPGroup' hAut hZ hno W hW hunique,
    hC.card_omega_center_eq_two_or_four_of_unique_four S.isPGroup' hZ hno W hW hunique⟩

/-- A critical subgroup whose center is elementary with omega four has all
of the structural core properties required by the order-sixteen argument. -/
public theorem critical_center_data_of_omega_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C)
    (hfour : Nat.card (omega₁ (center C) (p := 2)) = 4)
    [IsElementaryAbelian 2 (center C)] :
    IsCriticalPSubgroup 2 C ∧ Nat.card (center C) = 4 ∧
      IsElementaryAbelian 2 (center C) ∧
      (∀ x : C, x ^ 2 = 1 → x ∈ center C) := by
  exact ⟨hC, IsCriticalPSubgroup.card_center_eq_four_of_elementary_of_omega_center_four hfour,
    inferInstance,
    hC.square_one_mem_center_of_unique_four_of_omega_center_four hno W hW hunique hfour⟩

/-- The central-two outer-normalizer branch has a critical subgroup with
elementary center of order four and with every involution central. -/
public theorem exists_critical_subgroup_elementary_center_four
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧ Nat.card (center C) = 4 ∧
      IsElementaryAbelian 2 (center C) ∧
      (∀ x : C, x ^ 2 = 1 → x ∈ center C) := by
  obtain ⟨C, hC, hfour⟩ :=
    NormalEightExoticCriticalCenterOmega.exists_critical_center_omega_four S hno W hW hunique
  have hCnonab := hC.not_isMulCommutative_of_unique_four_of_omega_center_two
    S.isPGroup' (S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm)
    hZ hno W hW hunique
  let : IsElementaryAbelian 2 (center C) :=
    NormalEightExoticCriticalCenterExponent.center_elementary_of_omega_four
      S hnorm hZ hno W hW hunique C hC hCnonab hfour
  exact ⟨C, critical_center_data_of_omega_four S hno W hW hunique C hC hfour⟩

end Stellmacher.Recognition.NormalEightExoticCriticalCenter
