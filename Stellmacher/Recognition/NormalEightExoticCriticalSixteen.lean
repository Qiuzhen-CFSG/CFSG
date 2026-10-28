module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.UniqueNormalFourCritical
public import Theory.GroupTheory.SylowPGroupAutomizer
public import Stellmacher.Recognition.NormalEightExoticCriticalCenter
public import Theory.GroupTheory.PGroup.CentralInvolutionCriticalSixteen

/-!
# A critical subgroup of order sixteen in the central-two exotic branch

The nontrivial outer normalizer action makes the Sylow automorphism group
not a two-group. A characteristic critical subgroup exists; its first
omega is elementary of order two or four and lies in the unique normal
four. Its derived subgroup is central in the Sylow subgroup.

The structural critical-center theorem supplies a critical subgroup with
elementary center of order four and central involutions. The intrinsic order
calculation then makes this subgroup have order sixteen whenever the Sylow
subgroup contains a subgroup of order sixteen. This construction needs no
ambient simplicity, nonsolvability, N₂ condition, fusion assumption, or
elementarity assumption on the subgroup of order sixteen.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3, printed p.386,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace Stellmacher.Recognition.NormalEightExoticCriticalSixteen

open Subgroup

/-- The central-two outer branch has a critical subgroup whose elementary
omega has order two or four and is contained in the unique normal four. -/
public theorem exists_critical_subgroup_data
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W) :
    ¬ IsPGroup 2 (MulAut S) ∧
      ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧
        IsElementaryAbelian 2 (omega₁ C (p := 2)) ∧
        (Nat.card (omega₁ C (p := 2)) = 2 ∨ Nat.card (omega₁ C (p := 2)) = 4) ∧
        (omega₁ C (p := 2)).map C.subtype ≤ W ∧ ⁅C, C⁆ ≤ center S := by
  obtain ⟨C, hC⟩ := S.isPGroup'.exists_criticalPSubgroup
  exact ⟨S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm,
    C, hC, hC.omega_one_elementary_of_unique_four hno W hW hunique,
    hC.card_omega_one_eq_two_or_four_of_unique_four S.isPGroup' hZ hno W hW hunique,
    hC.omega_one_map_le_unique_four hno W hW hunique,
    hC.commutator_self_le_ambient_center⟩

/-- The central-two outer-normalizer branch contains a critical subgroup of
order sixteen with elementary center of order four and central involutions.
The subgroup of order sixteen need not be elementary abelian. -/
public theorem exists_critical_subgroup_order_sixteen
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (B : Subgroup S) (hB : Nat.card B = 16) :
    ∃ C : Subgroup S, IsCriticalPSubgroup 2 C ∧ Nat.card C = 16 ∧
      Nat.card (center C) = 4 ∧ IsElementaryAbelian 2 (center C) ∧
      (∀ x : C, x ^ 2 = 1 → x ∈ center C) := by
  obtain ⟨C, hC, hCZ, hCElem, hinv⟩ :=
    NormalEightExoticCriticalCenter.exists_critical_subgroup_elementary_center_four
      S hnorm hZ hno W hW hunique
  let : IsElementaryAbelian 2 (center C) := hCElem
  exact ⟨C, hC, hC.card_eq_sixteen_of_elementary_center hZ B hB hCZ hinv,
    hCZ, hCElem, hinv⟩

end Stellmacher.Recognition.NormalEightExoticCriticalSixteen
