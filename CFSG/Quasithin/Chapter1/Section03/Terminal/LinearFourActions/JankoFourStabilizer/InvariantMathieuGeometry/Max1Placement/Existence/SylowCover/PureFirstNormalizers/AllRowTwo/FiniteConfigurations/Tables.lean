module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.FiniteConfigurations.RowGeometry

/-!
# Incidences between the literal native rows

The exact membership theorem reduces containment of native rows to inclusion
of their finite mask sets. These checked incidences show that row 5 is in none
of the listed sixteens and each other eight is in exactly two of them. This is
the candidate incidence table, not yet an identification of the unrestricted
ambient `sixteenOvergroups` family; that identification needs exhaustiveness
and the independent-pair condition on the ten sixteen rows.
Source: Kleidman--Wilson (1988), Section 2.1, pp.488--489.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
attribute [local irreducible] modelGroup matrixA matrixB

/-- The complete candidate incidence table, with zero-based sixteen indices. -/
theorem listedSixteenOvergroups_table : listedSixteenOvergroups = ![
  {0,6},
  {3,5},
  {2,4},
  {0,7},
  {8,9},
  {},
  {3,4},
  {2,6},
  {5,6},
  {1,8},
  {1,4},
  {3,7},
  {2,9},
  {0,1},
  {5,8},
  {7,9}] := by
  funext i
  have hc : ∀ i, listedSixteenOvergroups i = ![
    {0,6},
    {3,5},
    {2,4},
    {0,7},
    {8,9},
    {},
    {3,4},
    {2,6},
    {5,6},
    {1,8},
    {1,4},
    {3,7},
    {2,9},
    {0,1},
    {5,8},
    {7,9}] i := by decide +kernel
  exact hc i

theorem eight_card (i : Fin 16) : Nat.card (row (eightIndex i)) = 8 := by
  rw [row_card,if_pos]
  exact i.isLt

theorem sixteen_card (i : Fin 10) : Nat.card (row (sixteenIndex i)) = 16 := by
  rw [row_card,if_neg]
  change ¬ 16 + i.val < 16
  omega

/-- Actual native containment is equivalent to membership in the checked table. -/
theorem eight_le_sixteen_iff (i : Fin 16) (j : Fin 10) :
    row (eightIndex i) ≤ row (sixteenIndex j) ↔ j ∈ listedSixteenOvergroups i := by
  rw [row_le_iff]
  simp only [listedSixteenOvergroups,Finset.mem_filter,Finset.mem_univ,true_and]

theorem listedSixteenOvergroups_card (i : Fin 16) :
    (listedSixteenOvergroups i).card = if i = 5 then 0 else 2 := by
  have hc : ∀ i, (listedSixteenOvergroups i).card = if i = 5 then 0 else 2 := by
    rw [listedSixteenOvergroups_table]
    decide +kernel
  exact hc i

/-- The exceptional eight has no containment in any of the ten listed sixteens. -/
theorem line_not_le_listed_sixteen (j : Fin 10) : ¬ row 5 ≤ row (sixteenIndex j) := by
  have he : eightIndex 5 = 5 := rfl
  rw [← he,eight_le_sixteen_iff,listedSixteenOvergroups_table]
  exact Finset.notMem_empty j

/-- Each other listed eight has exactly two distinct listed sixteen overgroups. -/
theorem two_listed_sixteens (i : Fin 16) (hi : i ≠ 5) :
    ∃ j k : Fin 10, j ≠ k ∧
      ∀ l : Fin 10, row (eightIndex i) ≤ row (sixteenIndex l) ↔ l = j ∨ l = k := by
  have hc : ∀ i : Fin 16, i ≠ 5 → ∃ j k : Fin 10, j ≠ k ∧
      ∀ l : Fin 10, l ∈ listedSixteenOvergroups i ↔ l = j ∨ l = k := by
    rw [listedSixteenOvergroups_table]
    decide +kernel
  obtain ⟨j,k,hjk,h⟩ := hc i hi
  exact ⟨j,k,hjk,fun l => (eight_le_sixteen_iff i l).trans (h l)⟩

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo.FiniteConfigurations
