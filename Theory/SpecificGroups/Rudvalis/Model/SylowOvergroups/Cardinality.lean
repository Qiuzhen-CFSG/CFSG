module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level1
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level2
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level3
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level4
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level5
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level6
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level7
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level8
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Level9
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level1
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level2
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level3
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level4
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level5
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level6
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level7
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Level8
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max4Comparison
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.Cardinality.Max6Comparison
import Mathlib.Tactic.FinCases

/-!
# Orders of the two concrete Rudvalis Sylow-overgroup candidates

The ATLAS programs retained in `SylowOvergroups/source/` define the two
subgroups inside the existing Rudvalis model. Their images in the ambient
permutation group have certified Schreier chains of indices
`[28, 3, 2, 8, 2, 2, 4, 2, 4, 2]` and `[12, 10, 8, 2, 2, 4, 2, 4, 2]`.
Their terminal subgroups are trivial. Multiplying the indices gives the exact
orders and hence the two nondivisibility facts needed by the Sylow-pair argument.

The comparison with the original carrier is proved before transporting orders.
GAP supplies only witnesses: all inverse laws, generator comparisons, Schreier
transitions, orbit separation and stabilizer fixation are checked in Lean.

Source: GLS3, Table 5.3r, printed p.279, and the attributed ATLAS subgroup
programs documented in `SylowOvergroups.Definitions`.
-/

namespace Rudvalis.SylowOvergroups
open Theory.GroupTheory LocalCardinality

/-- Exact order of the subgroup defined by ATLAS program `RuG1-max4W1`. -/
public theorem max4_card : Nat.card max4 = 344064 := by
  have hword := wordSubgroup_eq_pair Max4.L0.gen Max4.L0.invOf Max4.L0.gen_inv
    (Max4.L0.gen_inv 0) (Max4.L0.gen_inv 1)
  calc
    Nat.card max4 = Nat.card (Subgroup.closure
        ({modelSubgroup.subtype max4Generators.1,
          modelSubgroup.subtype max4Generators.2} : Set (Equiv.Perm (Fin 4060)))) :=
      card_closure_pair _ _
    _ = Nat.card Max4.L0.subgroup := by
      rw [← Max4.generator0_eq, ← Max4.generator1_eq, ← hword]
      rfl
    _ = 344064 := by
      rw [Max4.L0.card_step, Max4.L1.card_step, Max4.L2.card_step, Max4.L3.card_step, Max4.L4.card_step, Max4.L5.card_step, Max4.L6.card_step, Max4.L7.card_step, Max4.L8.card_step, Max4.L9.card_step, Max4.L10.card]

/-- The local subgroup order contains only one factor of three. -/
public theorem not_nine_dvd_max4_card : ¬ 9 ∣ Nat.card max4 := by
  rw [max4_card]
  decide

/-- Exact order of the subgroup defined by ATLAS program `RuG1-max6W1`. -/
public theorem max6_card : Nat.card max6 = 245760 := by
  have hword := wordSubgroup_eq_pair Max6.L0.gen Max6.L0.invOf Max6.L0.gen_inv
    (Max6.L0.gen_inv 0) (Max6.L0.gen_inv 1)
  calc
    Nat.card max6 = Nat.card (Subgroup.closure
        ({modelSubgroup.subtype max6Generators.1,
          modelSubgroup.subtype max6Generators.2} : Set (Equiv.Perm (Fin 4060)))) :=
      card_closure_pair _ _
    _ = Nat.card Max6.L0.subgroup := by
      rw [← Max6.generator0_eq, ← Max6.generator1_eq, ← hword]
      rfl
    _ = 245760 := by
      rw [Max6.L0.card_step, Max6.L1.card_step, Max6.L2.card_step, Max6.L3.card_step, Max6.L4.card_step, Max6.L5.card_step, Max6.L6.card_step, Max6.L7.card_step, Max6.L8.card_step, Max6.L9.card]

/-- The local subgroup order contains only one factor of three. -/
public theorem not_nine_dvd_max6_card : ¬ 9 ∣ Nat.card max6 := by
  rw [max6_card]
  decide

end Rudvalis.SylowOvergroups
