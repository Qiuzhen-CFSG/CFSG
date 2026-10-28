module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.MatrixGeneration
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.CosetCover
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound
public import Theory.SpecificGroups.SymplecticSix.OrderRank

/-!
# Faithfulness of the seven-relator Sp₆(2) presentation

The kernel-checked 36-coset cover and the proved finite order bound 40320
for the actual subgroup ⟨a, bab³⟩ bound the presentation's order by 1451520.
The proved order of the literal matrix group, together with the existing
surjection, then proves injectivity. All subgroup-bound premises are
discharged; no subgroup identification or matrix-image order is assumed.

Source: ATLAS `S62G1-P1.M`, subgroup M2. This supplies the presentation
input to the universal-cover calculation for Aschbacher–Smith I.1.1.
-/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation

/-- The checked coset cover reduces the literal map's injectivity to a subgroup bound. -/
theorem matrixMap_injective_of_s8Subgroup_bound
    (h : Finite Faithfulness.s8Subgroup ∧ Nat.card Faithfulness.s8Subgroup ≤ 40320) :
    Function.Injective matrixMap := by
  obtain ⟨hf, hb⟩ := Faithfulness.presented_finite_card_le_of_subgroup_bound h
  let : Finite Presented := hf
  apply (matrixMap_surjective.bijective_of_nat_card_le ?_).1
  have hcard : Nat.card Base = 1451520 :=
    card_sp_of_card_two (by simp)
  rw [hcard]
  exact hb

/-- The literal seven-relator ATLAS presentation maps faithfully to Sp₆(2). -/
theorem matrixMap_injective : Function.Injective matrixMap :=
  matrixMap_injective_of_s8Subgroup_bound Faithfulness.SubgroupBound.s8Subgroup_bound

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation
