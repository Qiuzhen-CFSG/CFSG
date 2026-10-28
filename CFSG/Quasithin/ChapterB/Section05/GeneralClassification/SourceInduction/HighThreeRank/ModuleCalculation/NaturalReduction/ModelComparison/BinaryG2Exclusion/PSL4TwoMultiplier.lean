module

public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL4Two
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.MultiplierTable

/-!
# The proved L₄(2) row in the B.5 multiplier input

The genuine I.1.3(1) calculation supplies the literal row/value pair in
`MultiplierTable` and the order-divides-48 conclusion used by B.5's cover
construction. Only the L₄(2) branch is asserted here. The complete universal
`EarlierMultiplierInput`, including every other row and exhaustiveness,
remains the responsibility of the I.1 source assembly.

Source: Aschbacher–Smith, I.1.3(1), printed p.407, and B.5.7, pp.105–106.
The chapter dependency points from this B.5 application to its I.1 producer.
-/

public section

namespace CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion

open PerfectCentralCovering

universe u

/-- This genuine source calculation supplies the L₄(2) alternative in the
literal row/value contract consumed by B.5. It asserts no other table row. -/
theorem multiplier_two_row_of_isPSL_four_two
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (hS : ClassicalGroup.IsPSL S 4 2) :
    MultiplierRow S .two ∧
      Nonempty (schurMultiplier S ≃* MultiplierShape.two.Carrier) :=
  ⟨Or.inl hS, ChapterI.LieMultipliers.PSL4Two.schurMultiplier_equiv_two hS⟩

/-- The same row supplies B.5's exact numerical multiplier conclusion on
this source branch, independently of all other I.1.3 rows. -/
theorem multiplier_card_dvd_fortyEight_of_isPSL_four_two
    {S : Type u} [Group S] [Finite S] [Group.IsPerfect S]
    (hS : ClassicalGroup.IsPSL S 4 2) :
    Nat.card (schurMultiplier S) ∣ 48 := by
  rw [ChapterI.LieMultipliers.PSL4Two.schurMultiplier_card hS]
  norm_num

end CFSG.Quasithin.ChapterB.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion
