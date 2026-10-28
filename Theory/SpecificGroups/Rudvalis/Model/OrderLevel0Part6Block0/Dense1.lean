module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row25
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row26
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row27
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row28
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row29
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row30
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row31
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row32
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row33
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row34
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row35
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row36
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row37
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row38
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row39
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row40
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row41
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row42
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row43
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row44
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row45
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row46
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row47
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row48
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.Dense1.Row49
import Mathlib.Tactic.FinCases

/-!
# Rudvalis block-0 dense rows 25–49

Each row is certified by 203 slices of twenty points using the proved cached
factor maps. The row certificates therefore cover all 4060 points.
Source: the transition and factor witnesses in `FactorWords` and `OrderLevel0Data`.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense1
set_option Elab.async false

/-- All twenty-five transitions in the second dense block satisfy `stepCheck`. -/
public theorem checked (k : Fin 25) :
    stepCheck (FactorWords.row ⟨k.val + 25, by omega⟩).1
      (FactorWords.row ⟨k.val + 25, by omega⟩).2 := by
  fin_cases k
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30
  · exact row31
  · exact row32
  · exact row33
  · exact row34
  · exact row35
  · exact row36
  · exact row37
  · exact row38
  · exact row39
  · exact row40
  · exact row41
  · exact row42
  · exact row43
  · exact row44
  · exact row45
  · exact row46
  · exact row47
  · exact row48
  · exact row49

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.Dense1
