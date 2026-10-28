module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row0
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row1
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row2
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row3
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row4
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row5
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row6
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row7
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row8
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row9
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row10
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row11
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row12
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row13
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row14
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row15
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row16
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row17
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row18
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row19
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row20
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row21
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row22
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row23
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense0.Row24
import Mathlib.Tactic.FinCases

/-!
# First 25 dense transitions of Rudvalis part-6 block 0

Each row is certified on all 4060 points by twenty-point slices, using the
proved cached factor actions. This assembles rows 0–24 of FactorWords;
source data and representative words are checked in the row modules.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense0
set_option Elab.async false

/-- Dense rows 0–24 satisfy the original transition predicate. -/
public theorem checked (k : Fin 25) :
    stepCheck (FactorWords.row ⟨k.val, by omega⟩).1
      (FactorWords.row ⟨k.val, by omega⟩).2 := by
  fin_cases k
  · exact Row0.checked
  · exact Row1.checked
  · exact Row2.checked
  · exact Row3.checked
  · exact Row4.checked
  · exact Row5.checked
  · exact Row6.checked
  · exact Row7.checked
  · exact Row8.checked
  · exact Row9.checked
  · exact Row10.checked
  · exact Row11.checked
  · exact Row12.checked
  · exact Row13.checked
  · exact Row14.checked
  · exact Row15.checked
  · exact Row16.checked
  · exact Row17.checked
  · exact Row18.checked
  · exact Row19.checked
  · exact Row20.checked
  · exact Row21.checked
  · exact Row22.checked
  · exact Row23.checked
  · exact Row24.checked

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense0
