module
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import Theory.SpecificGroups.PSL2.BinaryPerfectCentralizer
public import Theory.GroupTheory.PCoreRestriction

/-!
# Two-cores above a normal perfect subgroup of odd PSL₂

Let B be a nontrivial normal perfect subgroup of H ≤ PSL₂(F), with F
finite of odd order. The two-core of B is trivial. The two-core of H
commutes with B, since their commutator lies in both B and O₂(H), hence
in O₂(B). The centralizer of B in PSL₂(F) is trivial, so O₂(H) is trivial.

The original Sylow intersection in the L₂(49) row of Aschbacher--Smith
12.5.3 consumes this result; it removes a possible two-group image kernel
without assuming any subfield marking of B. Source: printed pp.817--818,
using the odd-field PSL₂ centralizer results proved in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F]

/-- A subgroup of odd PSL₂ containing a nontrivial normal perfect subgroup has trivial two-core. -/
theorem twoCore_eq_bot_of_normal_perfect (hodd : Odd (Nat.card F))
    {B H : Subgroup PSL(2,F)} [Group.IsPerfect B] (hB : B ≠ ⊥)
    (hBH : B ≤ H) (hN : (B.subgroupOf H).Normal) : pCore 2 H = ⊥ := by
  have hnB : H ≤ normalizer (B : Set PSL(2,F)) :=
    (normal_subgroupOf_iff_le_normalizer hBH).mp hN
  have hnC : H ≤ normalizer (H.pCoreIn 2 : Set PSL(2,F)) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hcomm : ⁅H.pCoreIn 2,B⁆ ≤ B.pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 hBH)
    refine le_inf ?_ ?_
    · exact le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 H).trans hnB)
    · rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_right.mp (hBH.trans hnC)
  have hzero : ⁅H.pCoreIn 2,B⁆ = ⊥ := by
    apply bot_unique
    simpa only [pCoreIn,odd_perfect_subgroup_twoCore_eq_bot hodd B,Subgroup.map_bot] using hcomm
  have hc : H.pCoreIn 2 ≤ centralizer (B : Set PSL(2,F)) :=
    commutator_eq_bot_iff_le_centralizer.mp hzero
  rw [centralizer_eq_bot_of_perfect B hB] at hc
  exact ((pCore 2 H).map_eq_bot_iff_of_injective H.subtype_injective).mp (bot_unique hc)
end Theory.PSL2
